/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Tactic.Order
import Mathlib.Tactic.DepRewrite

-- TODO : ensure all material from Mathlib.RingTheory.Adjoin.PowerBasis is transferred
-- TODO : rewrite Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed to use my definitions

open Polynomial algebraMap

/-
## Preliminaries
-/

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
noncomputable abbrev liftOfSurjective (hf : Function.Surjective f) :
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

theorem eq_liftOfRightInverse (hf : Function.RightInverse f_inv f) (g : A →ₐ[R] C)
    (hg : RingHom.ker f ≤ RingHom.ker g) (h : B →ₐ[R] C) (hh : h.comp f = g) :
    h = f.liftOfRightInverse f_inv hf ⟨g, hg⟩ := by
  simp_rw [← hh]
  exact ((f.liftOfRightInverse f_inv hf).apply_symm_apply _).symm

end AlgHom

-- TODO : move these polynomial lemmas to the right place

-- TODO : replace non-primed version
theorem Polynomial.eq_of_monic_of_dvd_of_natDegree_le'
    {R : Type*} [Semiring R] {f g : R[X]}
    (hf : f.Monic) (hg : g.Monic) (h₁ : g ∣ f) (h₂ : f.natDegree ≤ g.natDegree) : f = g := by
  nontriviality R
  rcases h₁ with ⟨k, rfl⟩
  have : k ≠ 0 := fun hc ↦ by simp_all
  have : g.leadingCoeff * k.leadingCoeff ≠ 0 := by simp [*]
  rw [natDegree_mul' ‹_›] at h₂
  have : k.Monic := by simpa [leadingCoeff_mul' ‹_›, hg, Monic.def] using hf
  simp [Polynomial.eq_one_of_monic_natDegree_zero this (by omega)]

@[gcongr]
theorem Polynomial.aeval_dvd {S T : Type*} [CommSemiring S] [Semiring T] [Algebra S T]
    {p q : Polynomial S} (a : T) : p ∣ q → aeval a p ∣ aeval a q := _root_.map_dvd (aeval a)

-- TODO : replace non-primed version
theorem Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero'
    {S T : Type*} [CommSemiring S] [Semiring T] [Algebra S T]
    {p q : Polynomial S} (h₁ : p ∣ q) {a : T} (h₂ : (aeval a) p = 0) :
    (aeval a) q = 0 :=
  zero_dvd_iff.mp (h₂ ▸ aeval_dvd _ h₁)

theorem Polynomial.dvd_modByMonic_sub {R : Type*} [Ring R] (p q : R[X]) : q ∣ (p %ₘ q - p) := by
  by_cases h : q.Monic
  · simp [modByMonic_eq_sub_mul_div, h]
  · simp [modByMonic_eq_of_not_monic, h]

theorem Polynomial.dvd_iff_dvd_modByMonic {R : Type*} [Ring R] {p q : R[X]} :
    q ∣ p %ₘ q ↔ q ∣ p := by
  simpa using dvd_iff_dvd_of_dvd_sub <| dvd_modByMonic_sub p q

-- TODO : replace non-primed version
theorem Polynomial.aeval_modByMonic_eq_self_of_root'
    {R S : Type*} [CommRing R] [Ring S] [Algebra R S] (p : R[X]) {q : R[X]} {x : S}
    (hx : aeval x q = 0) : aeval x (p %ₘ q) = aeval x p := by
  simpa [sub_eq_zero, hx] using aeval_dvd x <| dvd_modByMonic_sub p q

theorem Polynomial.aeval_modByMonic_minpoly {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
    (p : R[X]) (x : S) : aeval x (p %ₘ minpoly R x) = aeval x p :=
  aeval_modByMonic_eq_self_of_root' _ (minpoly.aeval ..)

/-
## Lemmas about principal generators for an algebra
-/

namespace Algebra

variable (R : Type*) {S : Type*} [CommRing R] [Ring S] [Algebra R S] (x : S)

-- TODO : move to right place
theorem adjoin.isIntegral [Algebra.IsIntegral R S] (s : Set S) :
    Algebra.IsIntegral R ↥(Algebra.adjoin R s) :=
  (Subalgebra.isIntegral_iff _).mpr (fun x _ ↦ Algebra.IsIntegral.isIntegral x)

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

-- TODO : add version generalised to arbitrary set
include hx in
theorem finite_iff_isIntegral : Module.Finite R S ↔ IsIntegral R x where
  mp _ := _root_.IsIntegral.of_finite R x
  mpr h :=
    have := Algebra.finite_adjoin_simple_of_isIntegral h
    Module.Finite.equiv (adjoinEquiv hx).toLinearEquiv

noncomputable def repr (y : S) : R[X] := (aeval_surjective hx y).choose

@[simp]
theorem aeval_repr (y : S) : aeval x (repr hx y) = y :=
  (aeval_surjective hx y).choose_spec

theorem repr_aeval (f : R[X]) :
    repr hx (aeval x f) - f ∈ RingHom.ker (aeval x) := by simp

include hx in
theorem algHom_ext {S' : Type*} [Semiring S'] [Algebra R S']
    ⦃f g : S →ₐ[R] S'⦄ (h : f x = g x) : f = g := by
  ext y
  rw [← aeval_repr hx y, ← aeval_algHom_apply, ← aeval_algHom_apply, h]

end IsGenerator

theorem adjoin.isGenerator : IsGenerator R (⟨x, by aesop⟩ : ↥(adjoin R {x})) where
  adjoin_eq_top := Subalgebra.map_injective (f := (adjoin R {x}).val) Subtype.val_injective
    (by simp [Subalgebra.range_val])

variable {R} in
structure HasPrincipalKerAeval (g : R[X]) : Prop extends IsGenerator R x where
  ker_aeval : RingHom.ker (aeval (R := R) x) = Ideal.span {g}

namespace HasPrincipalKerAeval

variable {R x} {g : R[X]} (h : HasPrincipalKerAeval x g)

include h in
theorem aeval_self : aeval x g = 0 := by
  simp [← RingHom.mem_ker, h.ker_aeval, Ideal.mem_span_singleton_self]

variable {T : Type*} [Ring T] [Algebra R T] {y : T} (hy : aeval y g = 0)

include h hy in
theorem ker_aeval_le : RingHom.ker (aeval (R := R) x) ≤ RingHom.ker (aeval (R := R) y) :=
  fun _ hg ↦ aeval_eq_zero_of_dvd_aeval_eq_zero'
    (by simpa [h.ker_aeval, Ideal.mem_span_singleton] using hg) hy

-- TODO : incorporate bijection between maps out of `R[X]` and points in the codomain (via `aeval`)
--        then redefine `lift` using `liftEquiv` using the bijection in `AlgHom.liftOfRightInverse`

@[simps! -isSimp apply]
noncomputable def lift : S →ₐ[R] T :=
  AlgHom.liftOfRightInverse (aeval x) h.repr (fun _ ↦ by simp)
    ⟨aeval (R := R) y, h.ker_aeval_le hy⟩

@[simp]
theorem lift_aeval (f : R[X]) : h.lift hy (aeval x f) = aeval y f :=
  AlgHom.liftOfRightInverse_comp_apply ..

@[simp]
theorem lift_root : h.lift hy x = y := by simpa using h.lift_aeval hy X

theorem eq_lift {φ : S →ₐ[R] T} (hφ : φ x = y) : φ = h.lift hy := h.algHom_ext (by simp [hφ])

@[simps]
noncomputable def liftEquiv : (S →ₐ[R] T) ≃ { y : T // aeval y g = 0 } where
  toFun φ := ⟨φ x, by simp [Polynomial.aeval_algHom, h.aeval_self]⟩
  invFun y := h.lift y.2
  left_inv φ := (h.eq_lift _ (by simp)).symm
  right_inv y := by simp

end HasPrincipalKerAeval

/-
## Lemmas about *integral* principal generators for an algebra
-/

structure IsIntegralUnique : Prop where
  isIntegral : IsIntegral R x
  minpoly_dvd_of_root {f} (hf : aeval x f = 0) : minpoly R x ∣ f

namespace IsIntegralUnique

variable {R x}

theorem ker_aeval (h : IsIntegralUnique R x) :
    RingHom.ker (aeval x : _ →ₐ[R] S) = Ideal.span {minpoly R x} := by
  ext f
  simpa [Ideal.mem_span_singleton] using
    ⟨h.minpoly_dvd_of_root, fun h' ↦ aeval_eq_zero_of_dvd_aeval_eq_zero' h' (minpoly.aeval R x)⟩

theorem of_ker_aeval (isIntegral : IsIntegral R x)
    (h : RingHom.ker (aeval x : _ →ₐ[R] S) = Ideal.span {minpoly R x}) : IsIntegralUnique R x where
  isIntegral := isIntegral
  minpoly_dvd_of_root := fun hf ↦ by
    rw [← Ideal.mem_span_singleton, ← h, RingHom.mem_ker, hf]

theorem of_ker_aeval_eq_span_monic {g : R[X]} (hg : g.Monic)
    (h : RingHom.ker (aeval x : _→ₐ[R] S) = Ideal.span {g}) : IsIntegralUnique R x := by
  have hi : IsIntegral R x := ⟨g, hg, by simpa [← h] using Ideal.mem_span_singleton_self g⟩
  refine of_ker_aeval hi ?_
  rw [h, eq_of_monic_of_dvd_of_natDegree_le' (minpoly.monic hi) hg]
  · simp [← Ideal.mem_span_singleton, ← h]
  · exact Polynomial.natDegree_le_natDegree <| minpoly.min R x hg <| by
      simp [← RingHom.mem_ker, h, Ideal.mem_span_singleton_self]

theorem of_ker_aeval_eq_span [IsDomain R] {g : R[X]} (hx : IsIntegral R x)
    (h : RingHom.ker (aeval x : _→ₐ[R] S) = Ideal.span {g}) : IsIntegralUnique R x := by
  have dvd : g ∣ minpoly R x := by simp [← Ideal.mem_span_singleton, ← h]
  rcases dvd with ⟨k, hk⟩
  have hu : IsUnit g.leadingCoeff := IsUnit.of_mul_eq_one k.leadingCoeff <| by
    apply_fun leadingCoeff at hk
    simpa [minpoly.monic, hx] using hk.symm
  refine of_ker_aeval_eq_span_monic (g := C (↑hu.unit⁻¹ : R) * g) ?_ ?_
  · simpa [Units.smul_def, smul_eq_C_mul] using monic_of_isUnit_leadingCoeff_inv_smul hu
  · simpa [h, Ideal.span_singleton_eq_span_singleton] using
      associated_unit_mul_right _ _ (by simp [isUnit_C])

theorem unique_of_degree_le_degree_minpoly (h : IsIntegralUnique R x)
    {f : R[X]} (hmo : f.Monic) (hf : aeval x f = 0)
    (fmin : f.degree ≤ (minpoly R x).degree) : f = minpoly R x :=
  eq_of_monic_of_dvd_of_natDegree_le' hmo (minpoly.monic h.isIntegral) (h.minpoly_dvd_of_root hf)
    (natDegree_le_natDegree fmin)

theorem minpoly_unique (h : IsIntegralUnique R x)
    {f : R[X]} (hmo : f.Monic) (hf : aeval x f = 0)
    (hmin : ∀ g : R[X], g.Monic → aeval x g = 0 → f.degree ≤ g.degree) :
    f = minpoly R x :=
  unique_of_degree_le_degree_minpoly h hmo hf <|
    hmin (minpoly R x) (minpoly.monic h.isIntegral) (minpoly.aeval R x)

theorem of_unique_of_degree_le_degree_minpoly
    (isIntegral : IsIntegral R x)
    (h : ∀ f : R[X], f.Monic → aeval x f = 0 → f.degree ≤ (minpoly R x).degree → f = minpoly R x) :
    IsIntegralUnique R x where
  isIntegral := isIntegral
  minpoly_dvd_of_root {g} hg := by
    nontriviality R
    have := degree_modByMonic_lt g (minpoly.monic isIntegral)
    simpa [modByMonic_eq_zero_iff_dvd (minpoly.monic isIntegral), ← Ideal.mem_span_singleton] using
      h (minpoly R x + g %ₘ minpoly R x)
      (Monic.add_of_left (minpoly.monic isIntegral) ‹_›)
      (by simp_all [Polynomial.modByMonic_eq_sub_mul_div _ (minpoly.monic isIntegral)])
      (by rw [degree_add_eq_left_of_degree_lt ‹_›])

end IsIntegralUnique

variable {x} in
theorem adjoin.isIntegral_elem (hx : IsIntegral R x) :
    IsIntegral R (⟨x, by aesop⟩ : ↥(adjoin R {x})) :=
  ⟨minpoly R x, minpoly.monic hx, by simp⟩

variable {x} in
theorem adjoin.isIntegralUnique (hx : IsIntegralUnique R x) :
    IsIntegralUnique R (⟨x, by aesop⟩ : ↥(adjoin R {x})) :=
  IsIntegralUnique.of_ker_aeval_eq_span_monic (minpoly.monic hx.isIntegral) <| by
    have : RingHomClass.toRingHom (aeval x) =
             (RingHomClass.toRingHom (Subalgebra.val (Algebra.adjoin R {x}))).comp
             (RingHomClass.toRingHom (aeval ⟨x, by aesop⟩ : R[X] →ₐ[R] ↥(adjoin R {x}))) := by
      ext a
      simp
      simp
    rw [← hx.ker_aeval, AlgHom.ker_coe (aeval x), this, RingHom.ker_comp_of_injective,
        AlgHom.ker_coe]
    simp

@[nontriviality]
theorem IsIntegralUnique.subsingleton [Subsingleton S] : IsIntegralUnique R x where
  isIntegral := by simp [nontriviality]
  minpoly_dvd_of_root := by simp [nontriviality]

-- TODO : move to right place
theorem Field.isIntegralUnique {R S : Type*} [Field R] [Ring S] [Algebra R S] {x : R}
    (h₁ : IsIntegral R x) : IsIntegralUnique R x where
  isIntegral := h₁
  minpoly_dvd_of_root := minpoly.dvd R x

-- TODO : move to `Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed`
theorem IsIntegrallyClosed.isIntegralUnique
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [Algebra R S]
    [IsDomain S] [NoZeroSMulDivisors R S] [IsIntegrallyClosed R] {x : S}
    (h₁ : IsIntegral R x) : IsIntegralUnique R x where
  isIntegral := h₁
  minpoly_dvd_of_root := minpoly.isIntegrallyClosed_dvd h₁

structure IsPrimitiveElement : Prop extends
    IsGenerator R x, HasPrincipalKerAeval x (minpoly R x) where
  isIntegral : IsIntegral R x

variable {R x} in
theorem IsIntegralUnique.isPrimitiveElement (h : IsIntegralUnique R x) (hg : IsGenerator R x) :
    IsPrimitiveElement R x := ⟨hg, h.ker_aeval, h.isIntegral⟩

namespace IsPrimitiveElement

variable {R x} (h : IsPrimitiveElement R x)

include h in
theorem isIntegralUnique : IsIntegralUnique R x :=
  .of_ker_aeval_eq_span_monic (minpoly.monic h.isIntegral) (h.ker_aeval)

include h in
theorem minpoly_dvd_of_root {f} (hf : (aeval x) f = 0) : minpoly R x ∣ f :=
  h.isIntegralUnique.minpoly_dvd_of_root hf

section repr

include h in
theorem modByMonic_repr_aeval (g : R[X]) :
    h.repr (aeval x g) %ₘ minpoly R x = g %ₘ minpoly R x :=
  modByMonic_eq_of_dvd_sub (minpoly.monic h.isIntegral) (h.minpoly_dvd_of_root (by simp))

@[simps -isSimp apply]
noncomputable def reprLinear : S →ₗ[R] R[X] where
  toFun y := h.repr y %ₘ minpoly R x
  map_add' y z := by
    rw (occs := [1]) [← h.aeval_repr y, ← h.aeval_repr z, ← map_add, modByMonic_repr_aeval h,
                      add_modByMonic]
  map_smul' c y := by
    rw (occs := [1]) [RingHom.id_apply, ← h.aeval_repr y, ← map_smul, modByMonic_repr_aeval h,
                      ← smul_modByMonic]

@[simp]
theorem aeval_reprLinear (y : S) : aeval x (h.reprLinear y) = y := by
  simp [reprLinear_apply, aeval_modByMonic_minpoly]

@[simp]
theorem reprLinear_aeval (g : R[X]) : h.reprLinear (aeval x g) = g %ₘ minpoly R x := by
  simp [reprLinear_apply, h.modByMonic_repr_aeval]

theorem reprLinear_aeval_eq_self_iff [Nontrivial R] (g : R[X]) :
    h.reprLinear (aeval x g) = g ↔ g.degree < (minpoly R x).degree := by
  simpa using modByMonic_eq_self_iff (minpoly.monic h.isIntegral)

theorem reprLinear_aeval_eq_self {g : R[X]} (hg : g.degree < (minpoly R x).degree) :
    h.reprLinear (aeval x g) = g := by
  nontriviality R
  exact (h.reprLinear_aeval_eq_self_iff _).mpr hg

@[simp]
theorem reprLinear_root_pow {n : ℕ} (hdeg : n < (minpoly R x).natDegree) :
    h.reprLinear (x ^ n) = X ^ n := by
  nontriviality R
  rw [← h.reprLinear_aeval_eq_self (g := X ^ n) (by simpa using hdeg)]
  simp

@[simp]
theorem reprLinear_root (hdeg : 1 < (minpoly R x).natDegree) : h.reprLinear x = X := by
  simpa using h.reprLinear_root_pow hdeg

@[simp]
theorem reprLinear_one [Nontrivial S] : h.reprLinear 1 = 1 := by
  simpa using h.reprLinear_root_pow (minpoly.natDegree_pos h.isIntegral)

@[simp]
theorem reprLinear_algebraMap [Nontrivial S] (r : R) :
    h.reprLinear (algebraMap R S r) = algebraMap R R[X] r := by
  simp [Algebra.algebraMap_eq_smul_one, smul_eq_C_mul]

theorem degree_reprLinear_le [Nontrivial R] (y : S) :
    (h.reprLinear y).degree < (minpoly R x).degree :=
  degree_modByMonic_lt _ (minpoly.monic h.isIntegral)

theorem natDegree_reprLinear_le [Nontrivial S] (y : S) :
    (h.reprLinear y).natDegree < (minpoly R x).natDegree := by
  exact natDegree_modByMonic_lt _ (minpoly.monic h.isIntegral) (minpoly.ne_one R x)

theorem reprLinear_coeff_of_natDegree_le (y : S) {i : ℕ} (hi : (minpoly R x).natDegree ≤ i) :
    (h.reprLinear y).coeff i = 0 := by
  nontriviality R
  exact coeff_eq_zero_of_degree_lt <|
    by order [h.degree_reprLinear_le y, degree_le_of_natDegree_le hi]

end repr

section lift

variable {T : Type*} [CommRing T] [IsDomain T] [Algebra R T]

noncomputable def liftEquivAroots :
    (S →ₐ[R] T) ≃ { y : T // y ∈ (minpoly R x).aroots T } :=
  h.liftEquiv.trans <| (Equiv.refl _).subtypeEquiv fun x => by
    simp [map_monic_ne_zero (minpoly.monic h.isIntegral)]

@[simp]
theorem liftEquivAroots_apply (φ : S →ₐ[R] T) :
    h.liftEquivAroots φ = φ x := by simp [liftEquivAroots]

@[simp]
theorem liftEquivAroots_symm_apply_apply {y : T} (hy : y ∈ (minpoly R x).aroots T) (z : S) :
    h.liftEquivAroots.symm ⟨y, hy⟩ z = h.lift (y := y) (by simp_all) z := by simp [liftEquivAroots]

noncomputable def AlgHom.fintype : Fintype (S →ₐ[R] T) :=
  letI := Classical.decEq T
  Fintype.ofEquiv _ h.liftEquivAroots.symm

end lift

section equiv

variable {S' : Type*} [Ring S'] [Algebra R S'] {x' : S'} (h' : IsPrimitiveElement R x')

section root

variable (hx : aeval x (minpoly R x') = 0) (hx' : aeval x' (minpoly R x) = 0)

@[simps! -isSimp apply]
noncomputable def equivOfRoot : S ≃ₐ[R] S' :=
  AlgEquiv.ofAlgHom (h.lift hx') (h'.lift hx)
    (by ext; simp [h'.lift_apply]) (by ext; simp [h.lift_apply])

@[simp]
theorem equivOfRoot_symm : (equivOfRoot h h' hx hx').symm = equivOfRoot h' h hx' hx := by
  ext; simp [equivOfRoot]

@[simp]
theorem equivOfRoot_aeval (f : R[X]): equivOfRoot h h' hx hx' (aeval x f) = aeval x' f := by
  simp [equivOfRoot_apply]

@[simp]
theorem equivOfRoot_root : equivOfRoot h h' hx hx' x = x' := by simp [equivOfRoot_apply]

end root

section minpoly

variable (hm : minpoly R x = minpoly R x')

noncomputable def equiv : S ≃ₐ[R] S' :=
  equivOfRoot h h' (by simp [← hm]) (by simp [hm])

@[simp]
theorem equiv_apply (z : S) :
    equiv h h' hm z = equivOfRoot h h' (by simp [← hm]) (by simp [hm]) z := by simp [equiv]

@[simp]
theorem equiv_symm : (equiv h h' hm).symm = equiv h' h hm.symm := by simp [equiv]

end minpoly

end equiv

section map

variable {T : Type*} [Ring T] [Algebra R T] (φ : S ≃ₐ[R] T)

noncomputable def map :
    IsPrimitiveElement R (φ x) where
  adjoin_eq_top := by
    have : (adjoin R {x}).map φ.toAlgHom = ⊤ := by
      simp [h.adjoin_eq_top, AlgHom.range_eq_top, AlgEquiv.surjective]
    simpa [AlgHom.map_adjoin φ.toAlgHom {x}]
  isIntegral := IsIntegral.map _ h.isIntegral
  ker_aeval := by
    rw [minpoly.algEquiv_eq, Polynomial.aeval_algEquiv, AlgHom.ker_coe, AlgHom.comp_toRingHom,
        AlgEquiv.coe_ringHom_commutes, ← RingEquiv.toRingHom_eq_coe, RingHom.ker_equiv_comp,
        RingHom.ker_coe_toRingHom, h.ker_aeval]

@[simp]
theorem equivOfRoot_map :
  equivOfRoot h (h.map φ) (by simp) (by rw [← minpoly.algEquiv_eq φ, minpoly.aeval]) = φ := by
    apply_fun AlgHomClass.toAlgHom using AlgEquiv.coe_algHom_injective
    exact h.algHom_ext (by simp)

end map

section basis

open Module

noncomputable def coeff : S →ₗ[R] ℕ → R :=
  { toFun := Polynomial.coeff, map_add' p q := by ext; simp, map_smul' c p := by ext; simp } ∘ₗ
  h.reprLinear

theorem coeff_apply_of_natDegree_le (z : S) (i : ℕ) (hi : (minpoly R x).natDegree ≤ i) :
    h.coeff z i = 0 := by
  nontriviality R
  simpa [coeff] using h.reprLinear_coeff_of_natDegree_le z hi

theorem coeff_root_pow {n} (hn : n < (minpoly R x).natDegree) :
    h.coeff (x ^ n) = Pi.single n 1 := by
  ext i
  simp [coeff, hn, Pi.single_apply]

theorem coeff_root (hdeg : 1 < natDegree (minpoly R x)) : h.coeff x = Pi.single 1 1 := by
  rw [← h.coeff_root_pow hdeg, pow_one]

@[simp]
theorem coeff_one [Nontrivial S] : h.coeff 1 = Pi.single 0 1 := by
  simp [← h.coeff_root_pow (minpoly.natDegree_pos h.isIntegral)]

@[simp]
theorem coeff_algebraMap [Nontrivial S] (r : R) : h.coeff (algebraMap R S r) = Pi.single 0 r := by
  ext i
  simpa [Algebra.algebraMap_eq_smul_one, Pi.smul_apply] using
    Pi.apply_single (fun _ s ↦ r * s) (by simp) 0 1 i

noncomputable def basis : Basis (Fin (minpoly R x).natDegree) R S := Basis.ofRepr
  { toFun y := (h.reprLinear y).toFinsupp.comapDomain _ Fin.val_injective.injOn
    invFun g := aeval x (ofFinsupp (g.mapDomain Fin.val))
    left_inv y := by
      simp only
      rw [Finsupp.mapDomain_comapDomain _ Fin.val_injective]
      · simp
      · intro i hi
        contrapose! hi
        simpa [toFinsupp_apply] using h.reprLinear_coeff_of_natDegree_le y (by simpa using hi)
    right_inv g := by
      nontriviality R
      ext i
      suffices { toFinsupp := Finsupp.mapDomain Fin.val g } %ₘ minpoly R x =
               { toFinsupp := Finsupp.mapDomain Fin.val g } by
        simpa [this] using Finsupp.mapDomain_apply Fin.val_injective ..
      rw [Polynomial.modByMonic_eq_self_iff (minpoly.monic h.isIntegral),
          degree_eq_natDegree (minpoly.ne_zero h.isIntegral), degree_lt_iff_coeff_zero]
      intro m hm
      simpa using Finsupp.mapDomain_notin_range _ _ (by simpa)
    map_add' := by simp [Finsupp.comapDomain_add_of_injective Fin.val_injective]
    map_smul' := by simp [Finsupp.comapDomain_smul_of_injective Fin.val_injective] }

@[simp]
theorem coe_basis : ⇑h.basis = fun i : Fin (minpoly R x).natDegree => x ^ (i : ℕ) := by
  simp [basis]

theorem basis_apply (i) : h.basis i = x ^ (i : ℕ) := by simp

theorem root_pow_eq_basis_apply {i} (hdeg : i < (minpoly R x).natDegree) :
    x ^ i = h.basis ⟨i, hdeg⟩ := by simp

theorem root_eq_basis_one (hdeg : 1 < (minpoly R x).natDegree) : x = h.basis ⟨1, hdeg⟩ := by simp

theorem one_eq_basis_zero [Nontrivial S] :
    1 = h.basis ⟨0, minpoly.natDegree_pos h.isIntegral⟩ := by simp

include h in
theorem free : Free R S := .of_basis h.basis

include h in
theorem finite : Module.Finite R S := .of_basis h.basis

include h in
theorem finrank_eq_natDegree [Nontrivial R] : finrank R S = (minpoly R x).natDegree := by
  rw [finrank_eq_card_basis h.basis, Fintype.card_fin]

include h in
theorem finrank_eq_degree [Nontrivial R] : finrank R S = (minpoly R x).degree := by
  rw [h.finrank_eq_natDegree, degree_eq_natDegree (minpoly.ne_zero h.isIntegral)]

set_option trace.order true
protected theorem leftMulMatrix : Algebra.leftMulMatrix h.basis x =
    @Matrix.of (Fin (minpoly R x).natDegree) (Fin (minpoly R x).natDegree) _ fun i j =>
      if ↑j + 1 = (minpoly R x).natDegree then -(minpoly R x).coeff i
      else if (i : ℕ) = j + 1 then 1
      else 0 := by
  nontriviality R
  rw [Algebra.leftMulMatrix_apply, ← LinearEquiv.eq_symm_apply]
  refine h.basis.ext fun k ↦ ?_
  rw [LinearMap.toMatrix_symm, Matrix.toLin_self]
  simp only [coe_lmul_eq_mul, coe_basis, LinearMap.mul_apply_apply, ← pow_succ', Matrix.of_apply,
             ite_smul, neg_smul, one_smul, zero_smul, Finset.sum_ite_irrel, Finset.sum_neg_distrib]
  split_ifs with h'
  · rw [h', eq_neg_iff_add_eq_zero, ← minpoly.aeval R x, aeval_eq_sum_range, add_comm,
        Finset.sum_range_succ, Finset.sum_range, coeff_natDegree,
        (minpoly.monic h.isIntegral).leadingCoeff, one_smul]
  · rw [Fintype.sum_eq_single ⟨k + 1, by omega⟩]
    · simp
    intro l hl
    contrapose! hl
    ext
    simp_all

theorem basis_repr_eq_coeff (y : S) (i : Fin _) :
    h.basis.repr y i = h.coeff y ↑i := by
  simp [basis, coeff, toFinsupp_apply]

theorem coeff_eq_basis_repr_of_lt_natDegree (z : S) (i : ℕ) (hi : i < (minpoly R x).natDegree) :
    h.coeff z i = h.basis.repr z ⟨i, hi⟩ := by simp [basis_repr_eq_coeff]

theorem coeff_eq_basis_repr (z : S) (i : ℕ) :
    h.coeff z i = if hi : i < natDegree (minpoly R x) then h.basis.repr z ⟨i, hi⟩ else 0 := by
  grind [coeff_apply_of_natDegree_le, coeff_eq_basis_repr_of_lt_natDegree]

theorem ext_elem ⦃y z : S⦄ (hyz : ∀ i < natDegree (minpoly R x), h.coeff y i = h.coeff z i) :
    y = z := h.basis.equivFun.injective (by ext; simp [hyz, basis_repr_eq_coeff])

theorem ext_elem_iff {y z : S} :
    y = z ↔ ∀ i < natDegree (minpoly R x), h.coeff y i = h.coeff z i := ⟨by grind, (h.ext_elem ·)⟩

theorem coeff_injective : Function.Injective h.coeff := fun _ _ hyz ↦ h.ext_elem (by simp [hyz])

end basis

theorem _root_.Algebra.adjoin.IsPrimitiveElement (hx : IsIntegralUnique R x) :
    IsPrimitiveElement R (⟨x, by aesop⟩ : ↥(adjoin R {x})) where
  __ := Algebra.adjoin.isIntegralUnique R hx
  __ := Algebra.adjoin.isGenerator R x

theorem of_basis [Module.Finite R S] {n} (B : Module.Basis (Fin n) R S) {x : S}
    (hB : ∀ i, B i = x ^ (i : ℕ)) : IsPrimitiveElement R x :=
  let f := X ^ n - ∑ i : Fin n, C (B.repr (x ^ n) i) * X ^ (i : ℕ)
  have aeval_f : aeval x f = 0 := by
      suffices x ^ n - ∑ i, (B.repr (x ^ n)) i • x ^ (i : ℕ) = 0 by simpa [f, ← Algebra.smul_def]
      rw (occs := [1]) [sub_eq_zero, ← B.linearCombination_repr (x ^ n),
                        Finsupp.linearCombination_apply, Finsupp.sum_fintype] <;>
      simp [hB]
  have f_monic : f.Monic := by
      nontriviality R
      apply (monic_X_pow _).sub_of_left _
      simp [degree_sum_fin_lt]
  { adjoin_eq_top := by
      rw [← toSubmodule_eq_top, _root_.eq_top_iff, ← B.span_eq, Submodule.span_le]
      rintro x ⟨i, rfl⟩
      aesop
    isIntegral := ⟨f, f_monic, aeval_f⟩
    ker_aeval := by
      nontriviality S
      nontriviality R using Algebra.subsingleton R S
      have n_pos : 0 < n := @Fin.pos' _ B.index_nonempty
      set f := X ^ n - ∑ i : Fin n, C (B.repr (x ^ n) i) * X ^ (i : ℕ) with f_def
      have f_deg : f.natDegree = n := natDegree_eq_of_degree_eq_some <| by
        rw [f_def, degree_sub_eq_left_of_degree_lt, degree_X_pow]
        simp [degree_sum_fin_lt]
      have f_monic : f.Monic := by
        apply (monic_X_pow _).sub_of_left _
        simp [degree_sum_fin_lt]
      have aeval_f : aeval x f = 0 := by
        suffices x ^ n - ∑ i, (B.repr (x ^ n)) i • x ^ (i : ℕ) = 0 by simpa [f, ← Algebra.smul_def]
        rw (occs := [1]) [sub_eq_zero, ← B.linearCombination_repr (x ^ n),
                          Finsupp.linearCombination_apply, Finsupp.sum_fintype] <;>
        simp [hB]
      exact Algebra.IsIntegralUnique.of_ker_aeval_eq_span_monic (x := x) f_monic <| by
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
  }

  __ : IsIntegralUnique R x := by


theorem of_free [Module.Finite R S] [Module.Free R S] (adjoin_eq_top : adjoin R {x} = ⊤) :
    IsPrimitiveElement R x := by
  refine of_basis
    (Module.Basis.mk (ι := Fin (Module.finrank R S)) (v := fun i ↦ x ^ (i : ℕ)) ?_ ?_)
    (fun i ↦ by rw [Module.Basis.coe_mk])
  · sorry
  · sorry
  -- prove that a spanning set of size `finrank R S` forms a basis (general nonsense)
  -- prove that `1, x, x ^ 2, ..., x ^ (d - 1)` spans by using tensors to reduce to `Field R`

end Algebra.IsPrimitiveElement

section IsAdjoinRootMonic

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S] {f : R[X]}

-- TODO : unify definition with (`Prop`-version of) `IsAdjoinRoot` or remove `IsAdjoinRoot`
variable (S f) in
noncomputable def IsAdjoinRootMonic : Prop :=
  ∃ x : S, Algebra.IsPrimitiveElement R x ∧ minpoly R x = f

variable (h : IsAdjoinRootMonic S f)

namespace IsAdjoinRootMonic

noncomputable def root := h.choose

theorem pe : Algebra.IsPrimitiveElement R h.root := h.choose_spec.1

@[simp] theorem minpoly_root : minpoly R h.root = f := h.choose_spec.2

include h in
theorem monic : f.Monic := by simpa using (minpoly.monic h.pe.isIntegral)

include h in
theorem degree_pos [Nontrivial S] : 0 < f.degree := by
  simpa using (minpoly.degree_pos h.pe.isIntegral)

include h in
theorem natDegree_pos [Nontrivial S] : 0 < f.natDegree := by
  simpa using (minpoly.natDegree_pos h.pe.isIntegral)

include h in
@[nontriviality]
theorem subsingleton [Subsingleton S] : f = 1 := by simpa using minpoly.subsingleton R h.root

-- TODO : figure out how to use nontriviality here
include h in
theorem nontrivial (hf : f ≠ 1) : Nontrivial S := by
  by_contra! hS
  exact hf (by simpa using minpoly.subsingleton R h.root)

noncomputable def lift {T : Type*} [Ring T] [Algebra R T] {y : T} (hy : aeval y f = 0) :
    S →ₐ[R] T := h.pe.lift (by simpa using hy)

noncomputable def liftEquiv {T : Type*} [Ring T] [Algebra R T] :
    (S →ₐ[R] T) ≃ { y : T // aeval y f = 0 } :=
  h.pe.liftEquiv.trans <| (Equiv.refl _).subtypeEquiv (by simp)

noncomputable def liftEquivAroots {T : Type*} [CommRing T] [IsDomain T] [Algebra R T] :
    (S →ₐ[R] T) ≃ { y : T // y ∈ f.aroots T } :=
  h.liftEquiv.trans <| (Equiv.refl _).subtypeEquiv fun x => by simp [map_monic_ne_zero h.monic]

noncomputable def AlgHom.fintype {T : Type*} [CommRing T] [IsDomain T] [Algebra R T] :
    Fintype (S →ₐ[R] T) :=
  letI := Classical.decEq T
  Fintype.ofEquiv _ h.liftEquivAroots.symm

noncomputable def equiv {T : Type*} [Ring T] [Algebra R T] (h' : IsAdjoinRootMonic T f):
    S ≃ₐ[R] T := h.pe.equiv h'.pe (by simp)

noncomputable def map {T : Type*} [Ring T] [Algebra R T] (φ : S ≃ₐ[R] T) : IsAdjoinRootMonic T f :=
  ⟨_, h.pe.map φ, by simp⟩

noncomputable def basis : Module.Basis (Fin f.natDegree) R S :=
  h.pe.basis.reindex (finCongr (by simp))

@[simp]
theorem coe_basis : ⇑h.basis = fun i : Fin f.natDegree => h.root ^ (i : ℕ) := by
  ext
  simp [basis]

theorem one_eq_basis_zero [Nontrivial S] : 1 = h.basis ⟨0, h.natDegree_pos⟩ := by simp

include h in theorem free : Module.Free R S := h.pe.free

include h in theorem finite : Module.Finite R S := h.pe.finite

include h in
theorem finrank_eq_natDegree [Nontrivial R] : Module.finrank R S = f.natDegree := by
  simpa using h.pe.finrank_eq_natDegree

include h in
theorem finrank_eq_degree [Nontrivial R] : Module.finrank R S = f.degree := by
  simpa using h.pe.finrank_eq_degree

end IsAdjoinRootMonic

end IsAdjoinRootMonic
