/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Tactic.DepRewrite

-- TODO : check out `Mathlib.LinearAlgebra.AnnihilatingPolynomial`: can we generalise it?

open Polynomial algebraMap

/-
## Preliminaries
-/

--TODO : move preliminaries to right places

-- TODO : make base ring argument in `Polynomial.aeval` explicit

namespace AlgHom

variable {R A B C : Type*} [CommRing R] [Ring A] [Ring B] [Ring C]
variable [Algebra R A] [Algebra R B] [Algebra R C]
variable (f : A →ₐ[R] B) (f_inv : B → A)

/-- Auxiliary definition used to define `liftOfRightInverse` -/
def liftOfRightInverseAux (hf : Function.RightInverse f_inv f) (g : A →ₐ[R] C)
    (hg : RingHom.ker f ≤ RingHom.ker g) :
    B →ₐ[R] C :=
  { RingHom.liftOfRightInverse f.toRingHom f_inv hf ⟨g.toRingHom, hg⟩ with
    toFun := fun b => g (f_inv b)
    commutes' := by
      intro r
      rw [← map_algebraMap g, ← sub_eq_zero, ← map_sub g, ← RingHom.mem_ker]
      apply hg
      rw [RingHom.mem_ker, map_sub f, sub_eq_zero, map_algebraMap f, hf _] }

@[simp]
theorem liftOfRightInverseAux_comp_apply (hf : Function.RightInverse f_inv f) (g : A →ₐ[R] C)
    (hg : RingHom.ker f ≤ RingHom.ker g) (a : A) :
    (f.liftOfRightInverseAux f_inv hf g hg) (f a) = g a :=
  f.toAddMonoidHom.liftOfRightInverse_comp_apply f_inv hf ⟨g.toAddMonoidHom, hg⟩ a

/-- `liftOfRightInverse f hf g hg` is the unique `R`-algebra homomorphism `φ`

* such that `φ.comp f = g` (`AlgHom.liftOfRightInverse_comp`),
* where `f : A →ₐ[R] B` has a right_inverse `f_inv` (`hf`),
* and `g : B →ₐ[R] C` satisfies `hg : f.ker ≤ g.ker`.

See `AlgHom.eq_liftOfRightInverse` for the uniqueness lemma.

```
   A .
   |  \
 f |   \ g
   |    \
   v     \⌟
   B ----> C
      ∃!φ
```
-/
def liftOfRightInverse (hf : Function.RightInverse f_inv f) :
    { g : A →ₐ[R] C // RingHom.ker f ≤ RingHom.ker g } ≃ (B →ₐ[R] C) where
  toFun g := f.liftOfRightInverseAux f_inv hf g.1 g.2
  invFun φ := ⟨φ.comp f, fun x hx => RingHom.mem_ker.mpr <| by simp [RingHom.mem_ker.mp hx]⟩
  left_inv g := by
    ext
    simp only [comp_apply, liftOfRightInverseAux_comp_apply]
  right_inv φ := by
    ext b
    simp [liftOfRightInverseAux, hf b]

/-- A non-computable version of `AlgHom.liftOfRightInverse` for when no computable right
inverse is available, that uses `Function.surjInv`. -/
@[simp]
noncomputable abbrev liftOfSurjective' (hf : Function.Surjective f) : -- TODO : replace `AlgHom.liftOfSurjective`
    { g : A →ₐ[R] C // RingHom.ker f ≤ RingHom.ker g } ≃ (B →ₐ[R] C) :=
  f.liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf)

theorem liftOfRightInverse_comp_apply (hf : Function.RightInverse f_inv f)
    (g : { g : A →ₐ[R] C // RingHom.ker f ≤ RingHom.ker g }) (x : A) :
    (f.liftOfRightInverse f_inv hf g) (f x) = g.1 x :=
  f.liftOfRightInverseAux_comp_apply f_inv hf g.1 g.2 x

theorem liftOfRightInverse_comp (hf : Function.RightInverse f_inv f)
    (g : { g : A →ₐ[R] C // RingHom.ker f ≤ RingHom.ker g }) :
    (f.liftOfRightInverse f_inv hf g).comp f = g :=
  AlgHom.ext <| f.liftOfRightInverse_comp_apply f_inv hf g

theorem liftOfRightInverse_symm (hf : Function.RightInverse f_inv f) (φ : B →ₐ[R] C) :
  (f.liftOfRightInverse f_inv hf).symm φ = φ.comp f := rfl

theorem eq_liftOfRightInverse (hf : Function.RightInverse f_inv f) (g : A →ₐ[R] C)
    (hg : RingHom.ker f ≤ RingHom.ker g) (h : B →ₐ[R] C) (hh : h.comp f = g) :
    h = f.liftOfRightInverse f_inv hf ⟨g, hg⟩ := by
  simp_rw [← hh]
  exact ((f.liftOfRightInverse f_inv hf).apply_symm_apply _).symm

end AlgHom

namespace Polynomial

@[gcongr]
theorem aeval_dvd {S T : Type*} [CommSemiring S] [Semiring T] [Algebra S T]
    {p q : Polynomial S} (a : T) : p ∣ q → p.aeval a ∣ q.aeval a := _root_.map_dvd (aeval a)

-- TODO : replace non-primed version
theorem aeval_eq_zero_of_dvd_aeval_eq_zero'
    {S T : Type*} [CommSemiring S] [Semiring T] [Algebra S T]
    {p q : Polynomial S} (h₁ : p ∣ q) {a : T} (h₂ : p.aeval a = 0) :
    q.aeval a = 0 :=
  zero_dvd_iff.mp (h₂ ▸ aeval_dvd _ h₁)

@[simp]
theorem modByMonic_self {R : Type*} [Ring R] {p : R[X]} (hp : p.Monic) : p %ₘ p = 0 := by
  rw [modByMonic_eq_zero_iff_dvd hp]

theorem dvd_modByMonic_sub {R : Type*} [Ring R] (p q : R[X]) : q ∣ (p %ₘ q - p) := by
  by_cases h : q.Monic
  · simp [modByMonic_eq_sub_mul_div, h]
  · simp [modByMonic_eq_of_not_monic, h]

theorem dvd_iff_dvd_modByMonic {R : Type*} [Ring R] {p q : R[X]} :
    q ∣ p %ₘ q ↔ q ∣ p := by
  simpa using dvd_iff_dvd_of_dvd_sub <| dvd_modByMonic_sub p q

-- TODO : replace non-primed version
theorem aeval_modByMonic_eq_self_of_root'
    {R S : Type*} [CommRing R] [Ring S] [Algebra R S] (p : R[X]) {q : R[X]} {x : S}
    (hx : q.aeval x = 0) : (p %ₘ q).aeval x = p.aeval x := by
  simpa [sub_eq_zero, hx] using aeval_dvd x <| dvd_modByMonic_sub p q

theorem aeval_modByMonic_minpoly {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
    (p : R[X]) (x : S) : (p %ₘ minpoly R x).aeval x = p.aeval x :=
  aeval_modByMonic_eq_self_of_root' _ (minpoly.aeval ..)

@[simp]
theorem aeval_apply_X {A B : Type*} [CommSemiring A] [Semiring B] [Algebra A B]
    (φ : A[X] →ₐ[A] B) : aeval (φ X) = φ := by ext; simp

theorem degree_sub_lt' {R : Type*} [Ring R] {p q : Polynomial R}
    (hd : p.degree = q.degree) (hq0 : q ≠ 0) (hlc : p.leadingCoeff = q.leadingCoeff) :
    (p - q).degree < q.degree := by
  rw [← degree_neg, neg_sub]
  exact degree_sub_lt hd.symm hq0 hlc.symm

lemma natDegree_le_of_monic_of_dvd {R : Type*} [Semiring R] {p q : R[X]}
    (hp : p.Monic) (hq : q ≠ 0) (hdvd : p ∣ q) : p.natDegree ≤ q.natDegree := by
  obtain ⟨r, rfl⟩ := hdvd
  obtain rfl | hr := eq_or_ne r 0
  · simp_all
  simp [hp.natDegree_mul' hr]

theorem eq_of_ideal_span_eq_of_monic {R : Type*} [CommSemiring R] {p q : R[X]}
    (hp : p.Monic) (hq : q.Monic) (h : Ideal.span {p} = Ideal.span {q}) : p = q := by
  nontriviality R
  have p_dvd_q := Ideal.span_singleton_le_span_singleton.mp (le_of_eq h.symm)
  have q_dvd_p := Ideal.span_singleton_le_span_singleton.mp (le_of_eq h)
  exact eq_of_monic_of_dvd_of_natDegree_le hq hp q_dvd_p
    (natDegree_le_of_monic_of_dvd hp hq.ne_zero p_dvd_q)

end Polynomial

theorem RingHom.subsingleton {R S : Type*} [Semiring R] [Semiring S]
    {f : R →+* S} : f 1 = 0 ↔ Subsingleton S := by
  rw [map_one, eq_comm, ← subsingleton_iff_zero_eq_one]

theorem RingHom.ker_eq_top_iff {R S : Type*} [Semiring R] [Semiring S]
    {f : R →+* S} : RingHom.ker f = ⊤ ↔ Subsingleton S := by
  rw [Ideal.eq_top_iff_one, mem_ker, RingHom.subsingleton]

alias ⟨RingHom.subsingleton_of_ker_eq_top, _⟩ :=
  RingHom.ker_eq_top_iff

-- TODO : replace unprimed version
@[nontriviality]
theorem RingHom.ker_eq_top_of_subsingleton' {R S : Type*} [Semiring R] [Semiring S]
    [Subsingleton S] {f : R →+* S} : RingHom.ker f = ⊤ := RingHom.ker_eq_top_iff.mpr inferInstance

section AlgHomEquiv

-- TODO : relate to `MonoidAlgebra.lift`?
@[simps]
noncomputable def Polynomial.AlgHomEquiv
    (A B : Type*) [CommSemiring A] [Semiring B] [Algebra A B] : B ≃ (A[X] →ₐ[A] B) where
  toFun y := aeval y
  invFun f := f X
  left_inv y := by simp
  right_inv f := by ext; simp

@[simps]
noncomputable def MvPolynomial.AlgHomEquiv
    (A B σ : Type*) [CommSemiring A] [CommSemiring B] [Algebra A B] :
    (σ → B) ≃ (MvPolynomial σ A →ₐ[A] B) where
  toFun y := aeval y
  invFun f i := f (X i)
  left_inv y := by simp
  right_inv f := by ext; simp

end AlgHomEquiv

section element

variable (R : Type*) {S : Type*} [CommRing R] [Ring S] [Algebra R S] (x : S)

/-
## Lemmas about principal generators for an algebra
-/

namespace Algebra

@[mk_iff IsGenerator.def]
structure IsGenerator : Prop where
  adjoin_eq_top : adjoin R {x} = ⊤

theorem isGenerator_iff_aeval_surjective :
    IsGenerator R x ↔ Function.Surjective (aeval x : R[X] →ₐ[R] S) := by
  rw [IsGenerator.def, adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top]

namespace IsGenerator

variable {R x} (hx : IsGenerator R x)

include hx in
theorem aeval_surjective : Function.Surjective (aeval x : R[X] →ₐ[R] S) :=
  (isGenerator_iff_aeval_surjective ..).mp hx

include hx in
noncomputable def adjoinEquiv : ↥(adjoin R {x}) ≃ₐ[R] S :=
  (Subalgebra.equivOfEq _ _ hx.adjoin_eq_top).trans Subalgebra.topEquiv

theorem adjoinEquiv_apply (y : ↥(adjoin R {x})) : adjoinEquiv hx y = ↑y := rfl

theorem adjoinEquiv_symm_apply (y : S) : (adjoinEquiv hx).symm y = y := rfl

include hx in
theorem finite_iff_isIntegral : Module.Finite R S ↔ IsIntegral R x where
  mp _ := _root_.IsIntegral.of_finite R x
  mpr h :=
    have := Algebra.finite_adjoin_simple_of_isIntegral h
    Module.Finite.equiv (adjoinEquiv hx).toLinearEquiv

include hx in
theorem of_root_mem_adjoin {y : S} (hy : x ∈ Algebra.adjoin R {y}) : IsGenerator R y where
  adjoin_eq_top := by
    rw [_root_.eq_top_iff, ← hx.adjoin_eq_top]
    exact adjoin_le (by simp [hy])

include hx in
theorem add_algebraMap (r : R) : IsGenerator R (x + (algebraMap _ _ r)) :=
  hx.of_root_mem_adjoin <| by
    nth_rw 2 [show x = x + (algebraMap _ _ r) - (algebraMap _ _ r) by simp]
    exact Subalgebra.sub_mem (adjoin R {x + (algebraMap _ _ r)}) (by aesop) (by aesop)

theorem algberaMap_mul {F : Type*} [Field F] [Algebra F S] {x : S} (hx : IsGenerator F x)
    {r : F} (hr : r ≠ 0) : IsGenerator F ((algebraMap _ _ r) * x) :=
  hx.of_root_mem_adjoin <| by
    nth_rw 2 [show x = (algebraMap _ _ r⁻¹) * ((algebraMap _ _ r) * x) by
      rw [← mul_assoc, ← map_mul]; simp [hr]]
    exact Subalgebra.mul_mem (adjoin F {algebraMap _ _ r * x}) (by aesop) (by aesop)

section liftEquiv

variable {T : Type*} [Ring T] [Algebra R T]

noncomputable def liftEquiv :
    { y : T // ∀ g : R[X], g.aeval x = 0 → g.aeval y = 0 } ≃ (S →ₐ[R] T) :=
  ((AlgHomEquiv R T).subtypeEquiv (by simp [SetLike.le_def])).trans <|
  AlgHom.liftOfSurjective' _ hx.aeval_surjective

@[simp]
theorem liftEquiv_symm_apply (φ : S →ₐ[R] T) :
    hx.liftEquiv.symm φ = φ x := by simp [liftEquiv, AlgHom.liftOfRightInverse_symm]

include hx in
theorem algHom_ext ⦃φ ψ : S →ₐ[R] T⦄ (h : φ x = ψ x) : φ = ψ := by
  rw [← Equiv.apply_eq_iff_eq hx.liftEquiv.symm]
  ext
  simp [h]

variable {y : T} (hy : ∀ g : R[X], g.aeval x = 0 → g.aeval y = 0)

@[simp]
theorem liftEquiv_aeval_apply (g : R[X]) : (hx.liftEquiv ⟨_, hy⟩) (g.aeval x) = g.aeval y := by
  simpa [liftEquiv] using AlgHom.liftOfRightInverse_comp_apply ..

@[simp]
theorem liftEquiv_comp_aeval : (hx.liftEquiv ⟨_, hy⟩).comp (aeval x) = aeval y := by
  simpa [liftEquiv] using AlgHom.liftOfRightInverse_comp ..

@[simp]
theorem liftEquiv_root : (hx.liftEquiv ⟨_, hy⟩) x = y := by
  simpa using hx.liftEquiv_aeval_apply hy X

-- TODO : liftEquiv_eq without unneccesary assumption

end liftEquiv

end IsGenerator

variable {R x} {g : R[X]}

theorem isUnit_iff_subsingleton_of_ker_aeval (h : RingHom.ker (aeval x) = Ideal.span {g}) :
    IsUnit g ↔ Subsingleton S := by
  rw [← Ideal.span_singleton_eq_top, ← h, ← RingHom.ker_coe_toRingHom, RingHom.ker_eq_top_iff]

alias ⟨subsingleton_of_ker_aeval, _⟩ := isUnit_iff_subsingleton_of_ker_aeval

theorem isUnit_of_ker_aeval [Subsingleton S] (h : RingHom.ker (aeval x) = Ideal.span {g}) :
    IsUnit g := (isUnit_iff_subsingleton_of_ker_aeval h).mpr inferInstance

theorem nontrivial_of_ker_aeval (h : RingHom.ker (aeval x) = Ideal.span {g}) (hg : ¬ IsUnit g) :
    Nontrivial S := by
  rw [isUnit_iff_subsingleton_of_ker_aeval h] at hg
  exact not_subsingleton_iff_nontrivial.mp hg

theorem not_isUnit_of_ker_aeval [Nontrivial S] (h : RingHom.ker (aeval x) = Ideal.span {g}) :
    ¬ IsUnit g := fun hc ↦ by
    rw [isUnit_iff_subsingleton_of_ker_aeval h] at hc
    exact false_of_nontrivial_of_subsingleton S

theorem aeval_eq_zero_iff_of_ker_aeval_eq_span_singleton
    (h : RingHom.ker (aeval x) = Ideal.span {g}) {f} : f.aeval x = 0 ↔ g ∣ f := by
  rw [← RingHom.mem_ker, h, Ideal.mem_span_singleton]

variable (x g)

@[mk_iff IsSimpleGenerator.def]
structure IsSimpleGenerator : Prop extends IsGenerator R x where
  ker_aeval : RingHom.ker (aeval x) = Ideal.span {g}

namespace IsSimpleGenerator

variable {x g} (h : IsSimpleGenerator x g)

include h in
theorem aeval_eq_zero_iff {f} : f.aeval x = 0 ↔ g ∣ f :=
  aeval_eq_zero_iff_of_ker_aeval_eq_span_singleton h.ker_aeval

include h in
theorem aeval_self : g.aeval x = 0 := by rw [h.aeval_eq_zero_iff]

variable {T : Type*} [Ring T] [Algebra R T]

include h in
theorem aeval_gen_eq_zero_iff (y : T) :
    g.aeval y = 0 ↔ ∀ f : R[X], f.aeval x = 0 → f.aeval y = 0 where
  mp hy f hf := aeval_eq_zero_of_dvd_aeval_eq_zero'
    (by simpa [h.aeval_eq_zero_iff] using hf) hy
  mpr hy := by
    simpa using hy g (by simp [h.aeval_eq_zero_iff])

section lift

noncomputable def liftEquiv :
    { y : T // g.aeval y = 0 } ≃ (S →ₐ[R] T) :=
  ((Equiv.refl _).subtypeEquiv fun y => by simpa using h.aeval_gen_eq_zero_iff y).trans <|
  h.toIsGenerator.liftEquiv

@[simp]
theorem liftEquiv_symm_apply (φ : S →ₐ[R] T) :
    h.liftEquiv.symm φ = φ x := by simp [liftEquiv]

variable {y : T} (hy : g.aeval y = 0)

noncomputable def lift : S →ₐ[R] T := h.liftEquiv ⟨_, hy⟩

@[simp]
theorem lift_aeval (f : R[X]) : h.lift hy (f.aeval x) = f.aeval y := by
  simp [lift, liftEquiv]

@[simp]
theorem lift_root : h.lift hy x = y := by simpa using h.lift_aeval hy X

-- TODO : liftEquiv_eq without unneccesary assumption

@[simp]
/- Make `lift` the preferred spelling -/
theorem liftEquiv_apply (z : S) : h.liftEquiv ⟨y, hy⟩ z = h.lift hy z := rfl

end lift

section equiv

variable {S' : Type*} [Ring S'] [Algebra R S'] {x' : S'} {g' : R[X]}

section root

variable (h' : IsSimpleGenerator x' g') (hx : g'.aeval x = 0) (hx' : g.aeval x' = 0)

@[simps! -isSimp apply]
noncomputable def equivOfRoot : S ≃ₐ[R] S' :=
  AlgEquiv.ofAlgHom (h.lift hx') (h'.lift hx)
    (h'.algHom_ext (by simp)) (h.algHom_ext (by simp))

@[simp]
theorem equivOfRoot_symm : (equivOfRoot h h' hx hx').symm = equivOfRoot h' h hx' hx := by
  ext; simp [equivOfRoot]

@[simp]
theorem equivOfRoot_aeval (f : R[X]): equivOfRoot h h' hx hx' (f.aeval x) = aeval x' f := by
  simp [equivOfRoot_apply]

@[simp]
theorem equivOfRoot_root : equivOfRoot h h' hx hx' x = x' := by simp [equivOfRoot_apply]

end root

section equal

variable (h' : IsSimpleGenerator x' g)

noncomputable def equiv : S ≃ₐ[R] S' :=
  equivOfRoot h h' h.aeval_self h'.aeval_self

@[simp]
theorem equiv_apply (z : S) :
    equiv h h' z = equivOfRoot h h' h.aeval_self h'.aeval_self z := by simp [equiv]

@[simp]
theorem equiv_symm : (equiv h h').symm = equiv h' h := by simp [equiv]

end equal

end equiv

section map

variable {T : Type*} [Ring T] [Algebra R T] (φ : S ≃ₐ[R] T)

noncomputable def map : IsSimpleGenerator (φ x) g where
  adjoin_eq_top := by
    have : (adjoin R {x}).map φ.toAlgHom = ⊤ := by
      simp [h.adjoin_eq_top, AlgHom.range_eq_top, AlgEquiv.surjective]
    simpa [AlgHom.map_adjoin φ.toAlgHom {x}]
  ker_aeval := by
    rw [Polynomial.aeval_algEquiv, AlgHom.ker_coe, AlgHom.comp_toRingHom,
        AlgEquiv.coe_ringHom_commutes, ← RingEquiv.toRingHom_eq_coe, RingHom.ker_equiv_comp,
        RingHom.ker_coe_toRingHom, h.ker_aeval]

@[simp]
theorem equivOfRoot_map :
    equivOfRoot h (h.map φ) h.aeval_self (by simpa [aeval_algEquiv] using h.aeval_self) = φ := by
  apply_fun AlgHomClass.toAlgHom using AlgEquiv.coe_algHom_injective
  exact h.algHom_ext (by simp)

end map

end Algebra.IsSimpleGenerator

open Algebra Polynomial

/-
## Lemmas about *integral* principal generators for an algebra
-/

variable {R} (g : R[X])

structure IsIntegralUnique : Prop where
  monic : g.Monic
  ker_aeval : RingHom.ker (aeval x : _ →ₐ[R] S) = Ideal.span {g}

namespace IsIntegralUnique

variable {x g}

variable (x g) in
@[nontriviality]
theorem of_subsingleton [Subsingleton R] : IsIntegralUnique x g where
  monic := by simp [nontriviality]
  ker_aeval := by simp [nontriviality]

variable (R x) in
@[nontriviality]
theorem of_subsingleton_gen_one [Subsingleton S] : IsIntegralUnique x (1 : R[X]) where
  monic := by simp
  ker_aeval := by rw [← RingHom.ker_coe_toRingHom]; simp [nontriviality]

theorem of_ker_aeval_eq_span_minpoly
    (hx : IsIntegral R x) (h : RingHom.ker (aeval x) = Ideal.span {minpoly R x}) :
    IsIntegralUnique x (minpoly R x) where
  monic := minpoly.monic hx
  ker_aeval := h

theorem of_ker_aeval_eq_span' [IsDomain R] (hx : IsIntegral R x)
    (h : RingHom.ker (aeval x) = Ideal.span {g}) :
    have hu : IsUnit g.leadingCoeff :=
      (minpoly.monic hx).isUnit_leadingCoeff_of_dvd (by simp [← Ideal.mem_span_singleton, ← h])
    IsIntegralUnique x (C (↑hu.unit⁻¹ : R) * g) where
  monic := by
    generalize_proofs
    simpa [Units.smul_def, smul_eq_C_mul] using monic_of_isUnit_leadingCoeff_inv_smul ‹_›
  ker_aeval := by
    simpa [h, Ideal.span_singleton_eq_span_singleton] using
      associated_unit_mul_right _ _ (by simp [isUnit_C])

-- TODO : fix proof
theorem of_ker_aeval_eq_span [IsDomain R] [NormalizationMonoid R] (hx : IsIntegral R x)
    (h : RingHom.ker (aeval x) = Ideal.span {g}) :
    IsIntegralUnique x (normalize g) := by
  have iu := of_ker_aeval_eq_span' hx h
  generalize_proofs pf at iu
  rcases pf with ⟨u, hu⟩
  simp [normalize, ← hu] at *
  rw [mul_comm]
  exact iu

theorem of_aeval_eq_zero_imp_minpoly_dvd (hx : IsIntegral R x)
    (h : ∀ {f}, f.aeval x = 0 → minpoly R x ∣ f) : IsIntegralUnique x (minpoly R x) where
  monic := minpoly.monic hx
  ker_aeval := by
    ext f
    simpa [Ideal.mem_span_singleton] using
      ⟨h, fun h' ↦ aeval_eq_zero_of_dvd_aeval_eq_zero' h' (minpoly.aeval R x)⟩

theorem of_unique_of_degree_le_degree_minpoly (hx : IsIntegral R x)
    (h : ∀ f : R[X], f.Monic → f.aeval x = 0 → f.degree ≤ (minpoly R x).degree → f = minpoly R x) :
    IsIntegralUnique x (minpoly R x) := of_aeval_eq_zero_imp_minpoly_dvd hx <| fun {g} hg ↦ by
  nontriviality R
  have := degree_modByMonic_lt g (minpoly.monic hx)
  simpa [modByMonic_eq_zero_iff_dvd (minpoly.monic hx), ← Ideal.mem_span_singleton] using
    h (minpoly R x + g %ₘ minpoly R x)
    (Monic.add_of_left (minpoly.monic hx) ‹_›)
    (by simp_all [Polynomial.modByMonic_eq_sub_mul_div _ (minpoly.monic hx)])
    (by rw [degree_add_eq_left_of_degree_lt ‹_›])

variable (h : IsIntegralUnique x g)

include h in
theorem aeval_eq_zero_iff {f} : f.aeval x = 0 ↔ g ∣ f :=
  aeval_eq_zero_iff_of_ker_aeval_eq_span_singleton h.ker_aeval

include h in
theorem aeval_gen : g.aeval x = 0 := by rw [h.aeval_eq_zero_iff]

include h in
theorem isIntegral : IsIntegral R x := ⟨g, h.monic, h.aeval_gen⟩

include h in
theorem gen_eq_one_iff_subsingleton : g = 1 ↔ Subsingleton S := by
  rw [← isUnit_iff_subsingleton_of_ker_aeval h.ker_aeval, h.monic.isUnit_iff]

alias ⟨subsingleton, _⟩ := gen_eq_one_iff_subsingleton

include h in
@[nontriviality]
theorem gen_eq_one [Subsingleton S] : g = 1 := h.gen_eq_one_iff_subsingleton.mpr inferInstance

include h in
theorem nontrivial (hg : g ≠ 1) : Nontrivial S := by
  rw [ne_eq, h.gen_eq_one_iff_subsingleton] at hg
  exact not_subsingleton_iff_nontrivial.mp hg

include h in
theorem gen_ne_one [Nontrivial S] : g ≠ 1 := fun hc ↦ by
  rw [h.gen_eq_one_iff_subsingleton] at hc
  exact false_of_nontrivial_of_subsingleton S

include h in
theorem natDegree_gen_pos [Nontrivial S] : 0 < g.natDegree := by
  by_contra hg
  exact h.gen_ne_one (eq_one_of_monic_natDegree_zero h.monic (by omega))

include h in
theorem degree_gen_pos [Nontrivial S] : 0 < g.degree :=
  natDegree_pos_iff_degree_pos.mp h.natDegree_gen_pos

include h in
theorem minpoly_eq_gen : minpoly R x = g := by
  rw [eq_of_monic_of_dvd_of_natDegree_le h.monic (minpoly.monic h.isIntegral)]
  · simp [← Ideal.mem_span_singleton, ← h.ker_aeval]
  · exact Polynomial.natDegree_le_natDegree <| minpoly.min _ x h.monic <| by
      simp [h.aeval_eq_zero_iff]

include h in
theorem gen_unique {g' : R[X]} (h' : IsIntegralUnique x g') : g = g' := by
  rw [← h.minpoly_eq_gen, ← h'.minpoly_eq_gen]

include h in
theorem irreducible_gen [IsDomain R] [IsDomain S] : Irreducible g := by
  rw [← h.minpoly_eq_gen]
  exact minpoly.irreducible h.isIntegral

include h in
theorem isIntegralUnique_minpoly : IsIntegralUnique x (minpoly R x) :=
  .of_ker_aeval_eq_span_minpoly h.isIntegral <| h.minpoly_eq_gen ▸ h.ker_aeval

include h in
theorem eq_gen_of_degree_le_degree_gen {f : R[X]} (hmo : f.Monic) (hf : f.aeval x = 0)
    (fmin : f.degree ≤ g.degree) : f = g :=
  eq_of_monic_of_dvd_of_natDegree_le h.monic hmo
    (h.aeval_eq_zero_iff.mp hf) (natDegree_le_natDegree fmin)

include h in
theorem eq_gen_of_aeval_eq_zero_imp_degree_ge {f : R[X]} (hmo : f.Monic) (hf : f.aeval x = 0)
    (hmin : ∀ k : R[X], k.Monic → k.aeval x = 0 → f.degree ≤ k.degree) : f = g :=
  eq_gen_of_degree_le_degree_gen h hmo hf <| hmin g h.monic h.aeval_gen

include h in
theorem eq_gen_of_ker_aeval_eq_span {f : R[X]} (hf : f.Monic)
    (hker : RingHom.ker (aeval x) = Ideal.span {f}) : f = g :=
  eq_of_ideal_span_eq_of_monic hf h.monic (by simp [← hker, h.ker_aeval])

include h in
theorem modByMonic_gen_eq_iff_aeval_eq (f₁ f₂ : R[X]) :
    f₁ %ₘ g = f₂ %ₘ g ↔ f₁.aeval x = f₂.aeval x := by
  rw [← sub_eq_zero, ← sub_modByMonic, modByMonic_eq_zero_iff_dvd h.monic,
      ← h.aeval_eq_zero_iff, map_sub, sub_eq_zero]

end IsIntegralUnique

structure IsIntegralUniqueGen : Prop extends
    IsSimpleGenerator x g, IsIntegralUnique x g

namespace IsIntegralUniqueGen

variable {x g}

theorem of_basis [Module.Finite R S] {n} (B : Module.Basis (Fin n) R S)
    (hB : ∀ i, B i = x ^ (i : ℕ)) :
    IsIntegralUniqueGen x (X ^ n - ∑ i : Fin n, C (B.repr (x ^ n) i) * X ^ (i : ℕ)) where
  __ : IsIntegralUnique x _ := by
    nontriviality R
    rcases subsingleton_or_nontrivial S with (hS | hS)
    · have : n = 0 := by
        rw [← Module.finrank_zero_of_subsingleton (R := R) (M := S),
            Module.finrank_eq_card_basis B, Fintype.card_fin]
      rw! (castMode := .all) [this]
      simp [nontriviality]
    have n_pos : 0 < n := @Fin.pos' _ B.index_nonempty
    set f := X ^ n - ∑ i : Fin n, C (B.repr (x ^ n) i) * X ^ (i : ℕ) with f_def
    have aeval_f : f.aeval x = 0 := by
      suffices x ^ n - ∑ i, (B.repr (x ^ n)) i • x ^ (i : ℕ) = 0 by simpa [f, ← Algebra.smul_def]
      rw (occs := [1]) [sub_eq_zero, ← B.linearCombination_repr (x ^ n),
                        Finsupp.linearCombination_apply, Finsupp.sum_fintype] <;>
      simp [hB]
    have f_monic : f.Monic := by
        nontriviality R
        apply (monic_X_pow _).sub_of_left _
        simp [degree_sum_fin_lt]
    have f_deg : f.natDegree = n := natDegree_eq_of_degree_eq_some <| by
      rw [f_def, degree_sub_eq_left_of_degree_lt, degree_X_pow]
      simp [degree_sum_fin_lt]
    refine ⟨f_monic, ?_⟩
    ext g
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    refine ⟨fun hg ↦ ?_, fun h ↦ by apply aeval_eq_zero_of_dvd_aeval_eq_zero' h aeval_f⟩
    nontriviality R
    have : (g %ₘ f).natDegree < n := by
      simpa [f_deg] using natDegree_modByMonic_lt g f_monic (fun hc ↦ by clear f_def; simp_all)
    rw [← modByMonic_eq_zero_iff_dvd f_monic,
        Polynomial.ext_iff_natDegree_le (n := n - 1) (by omega) (by simp)]
    rw [← aeval_modByMonic_eq_self_of_root f_monic aeval_f, ← B.forall_coord_eq_zero_iff,
        aeval_eq_sum_range' this, Finset.sum_range, Fin.forall_iff] at hg
    simp_rw [← hB, B.coord_apply, map_sum, map_smul, B.repr_self] at hg
    simpa [Finsupp.single_eq_pi_single, ← Nat.le_pred_iff_lt n_pos] using hg
  adjoin_eq_top := by
    rw [← toSubmodule_eq_top, _root_.eq_top_iff, ← B.span_eq, Submodule.span_le]
    rintro x ⟨i, rfl⟩
    aesop

theorem of_free [Module.Finite R S] [Module.Free R S] (hx : IsGenerator R x) :
    ∃ g' : R[X], IsIntegralUniqueGen x g' := by
  refine ⟨_, IsIntegralUniqueGen.of_basis
    (Module.Basis.mk (ι := Fin (Module.finrank R S)) (v := fun i ↦ x ^ (i : ℕ)) ?_ ?_)
    (fun i ↦ by rw [Module.Basis.coe_mk])⟩
  -- prove that a spanning set of size `finrank R S` is linearly independent (general nonsense)
  -- prove that `1, x, x ^ 2, ..., x ^ (d - 1)` spans by using tensors to reduce to `Field R`
  · sorry
  · sorry

variable (h : IsIntegralUniqueGen x g)

section repr

noncomputable def repr : S →ₗ[R] R[X] where
  toFun y := (Classical.choose (h.aeval_surjective y)) %ₘ g
  map_add' y z := by
    simp_rw [← add_modByMonic, h.modByMonic_gen_eq_iff_aeval_eq, map_add,
        Classical.choose_spec (h.aeval_surjective _)]
  map_smul' c y := by
    simp_rw [← smul_modByMonic, h.modByMonic_gen_eq_iff_aeval_eq, map_smul,
        Classical.choose_spec (h.aeval_surjective _), RingHom.id_apply]

@[simp]
theorem aeval_repr (y : S) : aeval x (h.repr y) = y := by
  simp [repr, aeval_modByMonic_eq_self_of_root' _ h.aeval_gen,
        Classical.choose_spec (h.aeval_surjective _)]

@[simp]
theorem repr_aeval (f : R[X]) : h.repr (f.aeval x) = f %ₘ g := by
  simp [repr, h.modByMonic_gen_eq_iff_aeval_eq,
        Classical.choose_spec (h.aeval_surjective _)]

theorem repr_aeval_eq_self_iff [Nontrivial R] (f : R[X]) :
    h.repr (f.aeval x) = f ↔ f.degree < g.degree := by
  simpa using modByMonic_eq_self_iff h.monic

theorem repr_aeval_eq_self {f : R[X]} (hf : f.degree < g.degree) :
    h.repr (f.aeval x) = f := by
  nontriviality R
  exact (h.repr_aeval_eq_self_iff _).mpr hf

@[simp]
theorem repr_root_pow {n : ℕ} (hdeg : n < g.natDegree) :
    h.repr (x ^ n) = X ^ n := by
  nontriviality R
  rw [← h.repr_aeval_eq_self (f := X ^ n) (by simpa using hdeg)]
  simp

@[simp]
theorem repr_root (hdeg : 1 < g.natDegree) : h.repr x = X := by
  simpa using h.repr_root_pow hdeg

@[simp]
theorem repr_one [Nontrivial S] : h.repr 1 = 1 := by
  simpa using h.repr_root_pow h.natDegree_gen_pos

@[simp]
theorem repr_algebraMap [Nontrivial S] (r : R) :
    h.repr (algebraMap R S r) = algebraMap R R[X] r := by
  simp [Algebra.algebraMap_eq_smul_one, smul_eq_C_mul]

@[simp]
theorem repr_ofNat [Nontrivial S] (n : ℕ) [Nat.AtLeastTwo n] :
    h.repr ofNat(n) = (n : R) := by simpa using h.repr_algebraMap n

@[simp]
theorem repr_root_pow_algebraMap :
    h.repr (x ^ g.natDegree) = X ^ g.natDegree - g := by
  nontriviality R
  rw [show x ^ g.natDegree = (X ^ g.natDegree : R[X]).aeval x by simp, repr_aeval,
      show X ^ g.natDegree %ₘ g = (X ^ g.natDegree - g) %ₘ g by simp [sub_modByMonic, h.monic],
      modByMonic_eq_self_iff h.monic]
  exact Polynomial.degree_sub_lt' (by simp [degree_eq_natDegree h.monic.ne_zero])
    h.monic.ne_zero (by simp [h.monic.leadingCoeff])

theorem degree_repr_le [Nontrivial R] (y : S) :
    (h.repr y).degree < g.degree :=
  degree_modByMonic_lt _ h.monic

theorem natDegree_repr_le [Nontrivial S] (y : S) :
    (h.repr y).natDegree < g.natDegree := by
  exact natDegree_modByMonic_lt _ h.monic h.gen_ne_one

theorem repr_coeff_of_natDegree_le (y : S) {i : ℕ} (hi : g.natDegree ≤ i) :
    (h.repr y).coeff i = 0 := by
  nontriviality R
  exact coeff_eq_zero_of_degree_lt <|
    by order [h.degree_repr_le y, degree_le_of_natDegree_le hi]

end repr

section lift

variable {T : Type*} [CommRing T] [IsDomain T] [Algebra R T]

noncomputable def liftEquivAroots :
    { y : T // y ∈ g.aroots T } ≃ (S →ₐ[R] T) :=
  ((Equiv.refl _).subtypeEquiv fun x => by
    simp [map_monic_ne_zero h.monic]).trans h.liftEquiv

@[simp]
theorem liftEquivAroots_symm_apply (φ : S →ₐ[R] T) :
    h.liftEquivAroots.symm φ = φ x := by simp [liftEquivAroots]

@[simp]
theorem liftEquivAroots_apply_apply {y : T} (hy : y ∈ g.aroots T) (z : S) :
    h.liftEquivAroots ⟨y, hy⟩ z = h.lift (y := y) (by simp_all) z := by simp [liftEquivAroots]

noncomputable def fintypeAlgHom : Fintype (S →ₐ[R] T) :=
  letI := Classical.decEq T
  Fintype.ofEquiv _ h.liftEquivAroots

end lift

section equiv

variable {S' : Type*} [Ring S'] [Algebra R S'] {x' : S'}

variable (h' : IsIntegralUniqueGen x' g)

noncomputable def equiv : S ≃ₐ[R] S' :=
  IsSimpleGenerator.equiv h.toIsSimpleGenerator h'.toIsSimpleGenerator

@[simp]
theorem equiv_apply (z : S) :
    equiv h h' z = IsSimpleGenerator.equiv
      h.toIsSimpleGenerator h'.toIsSimpleGenerator z := by
  simp [equiv]

@[simp]
theorem equiv_symm : (equiv h h').symm = equiv h' h := by simp [equiv]

end equiv

section map

variable {T : Type*} [Ring T] [Algebra R T] (φ : S ≃ₐ[R] T)

noncomputable def map : IsIntegralUniqueGen (φ x) g where
  __ : IsSimpleGenerator (φ x) g := h.toIsSimpleGenerator.map φ
  monic := h.monic

@[simp]
theorem equivOfRoot_map : h.equivOfRoot (h.map φ).toIsSimpleGenerator
    h.aeval_gen (h.map φ).aeval_gen = φ := by
  apply_fun AlgHomClass.toAlgHom using AlgEquiv.coe_algHom_injective
  exact h.algHom_ext (by simp)

end map

section basis

open Module

noncomputable def coeff : S →ₗ[R] ℕ → R :=
  { toFun := Polynomial.coeff, map_add' p q := by ext; simp, map_smul' c p := by ext; simp } ∘ₗ
  h.repr

theorem coeff_apply_of_natDegree_le (z : S) {i : ℕ} (hi : g.natDegree ≤ i) :
    h.coeff z i = 0 := by
  nontriviality R
  simpa [coeff] using h.repr_coeff_of_natDegree_le z hi

theorem coeff_root_pow {n} (hn : n < g.natDegree) :
    h.coeff (x ^ n) = Pi.single n 1 := by
  ext i
  simp [coeff, hn, Pi.single_apply]

theorem coeff_root_pow_natDegree {i : ℕ} (hi : i < g.natDegree) :
    h.coeff (x ^ g.natDegree) i = - g.coeff i := by
  simp [coeff, show i ≠ g.natDegree by omega]

theorem coeff_root (hdeg : 1 < g.natDegree) : h.coeff x = Pi.single 1 1 := by
  rw [← h.coeff_root_pow hdeg, pow_one]

@[simp]
theorem coeff_one [Nontrivial S] : h.coeff 1 = Pi.single 0 1 := by
  simp [← h.coeff_root_pow h.natDegree_gen_pos]

@[simp]
theorem coeff_algebraMap [Nontrivial S] (r : R) : h.coeff (algebraMap R S r) = Pi.single 0 r := by
  ext i
  simp [coeff, Polynomial.coeff_C, Pi.single_apply]

@[simp]
theorem coeff_ofNat [Nontrivial S] (n : ℕ) [Nat.AtLeastTwo n] :
    h.coeff ofNat(n) = Pi.single 0 (n : R) := by simpa using h.coeff_algebraMap n

noncomputable def basis : Basis (Fin g.natDegree) R S := Basis.ofRepr
  { toFun y := (h.repr y).toFinsupp.comapDomain _ Fin.val_injective.injOn
    invFun f := (ofFinsupp (f.mapDomain Fin.val)).aeval x
    left_inv y := by
      simp only
      rw [Finsupp.mapDomain_comapDomain _ Fin.val_injective]
      · simp
      · intro i hi
        contrapose! hi
        simpa [toFinsupp_apply] using h.repr_coeff_of_natDegree_le y (by simpa using hi)
    right_inv f := by
      nontriviality R
      ext i
      suffices { toFinsupp := Finsupp.mapDomain Fin.val f } %ₘ g =
               { toFinsupp := Finsupp.mapDomain Fin.val f } by
        simpa [this] using Finsupp.mapDomain_apply Fin.val_injective ..
      rw [Polynomial.modByMonic_eq_self_iff h.monic,
          degree_eq_natDegree h.monic.ne_zero, degree_lt_iff_coeff_zero]
      intro m hm
      simpa using Finsupp.mapDomain_notin_range _ _ (by simpa)
    map_add' := by simp [Finsupp.comapDomain_add_of_injective Fin.val_injective]
    map_smul' := by simp [Finsupp.comapDomain_smul_of_injective Fin.val_injective] }

@[simp]
theorem coe_basis : ⇑h.basis = fun i : Fin g.natDegree => x ^ (i : ℕ) := by
  simp [basis]

theorem basis_apply (i) : h.basis i = x ^ (i : ℕ) := by simp

theorem root_pow_eq_basis_apply {i} (hdeg : i < g.natDegree) :
    x ^ i = h.basis ⟨i, hdeg⟩ := by simp

theorem root_eq_basis_one (hdeg : 1 < g.natDegree) : x = h.basis ⟨1, hdeg⟩ := by simp

theorem one_eq_basis_zero [Nontrivial S] :
    1 = h.basis ⟨0, h.natDegree_gen_pos⟩ := by simp

include h in
theorem free : Free R S := .of_basis h.basis

include h in
theorem finite : Module.Finite R S := .of_basis h.basis

include h in
theorem finrank_eq_natDegree [Nontrivial R] : finrank R S = g.natDegree := by
  rw [finrank_eq_card_basis h.basis, Fintype.card_fin]

include h in
theorem finrank_eq_degree [Nontrivial R] : finrank R S = g.degree := by
  rw [h.finrank_eq_natDegree, degree_eq_natDegree h.monic.ne_zero]

set_option trace.order true
protected theorem leftMulMatrix : Algebra.leftMulMatrix h.basis x =
    @Matrix.of (Fin g.natDegree) (Fin g.natDegree) _ fun i j =>
      if ↑j + 1 = g.natDegree then -g.coeff i
      else if (i : ℕ) = j + 1 then 1
      else 0 := by
  nontriviality R
  rw [Algebra.leftMulMatrix_apply, ← LinearEquiv.eq_symm_apply]
  refine h.basis.ext fun k ↦ ?_
  rw [LinearMap.toMatrix_symm, Matrix.toLin_self]
  simp only [coe_lmul_eq_mul, coe_basis, LinearMap.mul_apply_apply, ← pow_succ', Matrix.of_apply,
             ite_smul, neg_smul, one_smul, zero_smul, Finset.sum_ite_irrel, Finset.sum_neg_distrib]
  split_ifs with h'
  · rw [h', eq_neg_iff_add_eq_zero, ← h.aeval_gen, aeval_eq_sum_range, add_comm,
        Finset.sum_range_succ, Finset.sum_range, coeff_natDegree,
        h.monic.leadingCoeff, one_smul]
  · rw [Fintype.sum_eq_single ⟨k + 1, by omega⟩]
    · simp
    intro l hl
    contrapose! hl
    ext
    simp_all

theorem basis_repr_eq_coeff (y : S) (i : Fin _) :
    h.basis.repr y i = h.coeff y ↑i := by
  simp [basis, coeff, toFinsupp_apply]

theorem coeff_eq_basis_repr_of_lt_natDegree (z : S) (i : ℕ) (hi : i < g.natDegree) :
    h.coeff z i = h.basis.repr z ⟨i, hi⟩ := by simp [basis_repr_eq_coeff]

theorem coeff_eq_basis_repr (z : S) (i : ℕ) :
    h.coeff z i = if hi : i < natDegree g then h.basis.repr z ⟨i, hi⟩ else 0 := by
  grind [coeff_apply_of_natDegree_le, coeff_eq_basis_repr_of_lt_natDegree]

theorem ext_elem ⦃y z : S⦄ (hyz : ∀ i < natDegree g, h.coeff y i = h.coeff z i) :
    y = z := h.basis.equivFun.injective (by ext; simp [hyz, basis_repr_eq_coeff])

theorem ext_elem_iff {y z : S} :
    y = z ↔ ∀ i < natDegree g, h.coeff y i = h.coeff z i := ⟨by grind, (h.ext_elem ·)⟩

theorem coeff_injective : Function.Injective h.coeff := fun _ _ hyz ↦ h.ext_elem (by simp [hyz])

end basis

end IsIntegralUniqueGen

end element

section IsAdjoinRoot'

variable {R : Type*} (S : Type*) [CommRing R] [Ring S] [Algebra R S] (f : R[X])

structure IsAdjoinRoot' : Prop where
  exists_root : ∃ x : S, Algebra.IsSimpleGenerator x f

namespace IsAdjoinRoot'

variable {S f} (h : IsAdjoinRoot' S f)

noncomputable def root := h.exists_root.choose

theorem pe : Algebra.IsSimpleGenerator h.root f := h.exists_root.choose_spec

noncomputable def liftEquiv {T : Type*} [Ring T] [Algebra R T] :
    { y : T // f.aeval y = 0 } ≃ (S →ₐ[R] T) :=
  ((Equiv.refl _).subtypeEquiv (by simp)).trans h.pe.liftEquiv

noncomputable def lift {T : Type*} [Ring T] [Algebra R T] {y : T} (hy : f.aeval y = 0) :
    S →ₐ[R] T := h.pe.lift (by simpa using hy)

noncomputable def equiv {T : Type*} [Ring T] [Algebra R T] (h' : IsAdjoinRoot' T f):
    S ≃ₐ[R] T := h.pe.equiv h'.pe

noncomputable def map {T : Type*} [Ring T] [Algebra R T] (φ : S ≃ₐ[R] T) :
    IsAdjoinRoot' T f where
  exists_root := ⟨_, by simpa using (h.pe.map φ)⟩

end IsAdjoinRoot'

structure IsAdjoinRootMonic' : Prop extends IsAdjoinRoot' S f where
  f_monic : f.Monic

namespace IsAdjoinRootMonic'

variable {S f} (h : IsAdjoinRootMonic' S f)

theorem ofIsIntegralUniqueGen {x : S} (hx : IsIntegralUniqueGen x f) : IsAdjoinRootMonic' S f :=
  ⟨⟨x, hx.toIsSimpleGenerator⟩, hx.monic⟩

theorem pe : IsIntegralUniqueGen h.root f where
  __ := h.exists_root.choose_spec
  monic := h.f_monic

@[simp]
theorem minpoly_root : minpoly R h.root = f := h.pe.minpoly_eq_gen

include h in
theorem irreducible [IsDomain R] [IsDomain S] : Irreducible f := h.pe.irreducible_gen

include h in
theorem subsingleton (hf : f = 1) : Subsingleton S := h.pe.gen_eq_one_iff_subsingleton.mp hf

include h in
theorem nontrivial (hf : f ≠ 1) : Nontrivial S := by
  by_contra! _
  exact hf h.pe.gen_eq_one

noncomputable def liftEquivAroots {T : Type*} [CommRing T] [IsDomain T] [Algebra R T] :
    { y : T // y ∈ f.aroots T } ≃ (S →ₐ[R] T) := h.pe.liftEquivAroots

noncomputable def fintypeAlgHom {T : Type*} [CommRing T] [IsDomain T] [Algebra R T] :
    Fintype (S →ₐ[R] T) := h.pe.fintypeAlgHom

noncomputable def map {T : Type*} [Ring T] [Algebra R T] (φ : S ≃ₐ[R] T) :
    IsAdjoinRootMonic' T f where
  __ := IsAdjoinRoot'.map h.toIsAdjoinRoot' φ
  f_monic := h.f_monic

include h in theorem free : Module.Free R S := h.pe.free

include h in theorem finite : Module.Finite R S := h.pe.finite

include h in
theorem finrank_eq_natDegree [Nontrivial R] : Module.finrank R S = f.natDegree :=
  h.pe.finrank_eq_natDegree

include h in
theorem finrank_eq_degree [Nontrivial R] : Module.finrank R S = f.degree :=
  h.pe.finrank_eq_degree

end IsAdjoinRootMonic'

end IsAdjoinRoot'
