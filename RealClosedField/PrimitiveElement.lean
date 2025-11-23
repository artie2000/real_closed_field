/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.PowerBasis
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Tactic.Order
import Mathlib.Tactic.DepRewrite

-- relevant file: Mathlib.RingTheory.Adjoin.PowerBasis

-- TODO : use this file to remove dependency of
--        Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed on AdjoinRoot

open Polynomial algebraMap

/-
## Lemmas about field adjoin vs ring adjoin
-/

-- TODO : move to `Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra`
-- the point is we prefer to say `Algebra.adjoin F {x} = ⊤` to `IntermediateField.adjoin F {x} = ⊤`
namespace IntermediateField

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

-- TODO : replace `IntermediateField.adjoin_algebraic_toSubalgebra` with this
theorem adjoin_integral_toSubalgebra {S : Set E} (hS : ∀ x ∈ S, IsIntegral F x) :
    (adjoin F S).toSubalgebra = Algebra.adjoin F S :=
  adjoin_eq_algebra_adjoin _ _ fun _ ↦ (Algebra.IsIntegral.adjoin (hS · ·)).inv_mem

@[simp]
theorem adjoin_toSubalgebra [Algebra.IsAlgebraic F E] (S : Set E) :
    (adjoin F S).toSubalgebra = Algebra.adjoin F S :=
  adjoin_integral_toSubalgebra (fun x _ ↦ Algebra.IsIntegral.isIntegral x)

-- TODO : the following should replace / subsume the existing unidirectional lemmas

theorem adjoin_integral_eq_top_iff {S : Set E} (hS : ∀ x ∈ S, IsIntegral F x) :
    adjoin F S = ⊤ ↔ Algebra.adjoin F S = ⊤ := by
  rw [← IntermediateField.adjoin_integral_toSubalgebra hS,
      ← IntermediateField.toSubalgebra_inj,
      IntermediateField.top_toSubalgebra]

theorem adjoin_simple_eq_top_iff_of_integral {x : E} (hx : IsIntegral F x) :
    F⟮x⟯ = ⊤ ↔ Algebra.adjoin F {x} = ⊤ := adjoin_integral_eq_top_iff (by simp [hx])

@[simp]
theorem adjoin_eq_top_iff [Algebra.IsAlgebraic F E] {S : Set E} :
    adjoin F S = ⊤ ↔ Algebra.adjoin F S = ⊤ :=
  adjoin_integral_eq_top_iff (fun x _ ↦ Algebra.IsIntegral.isIntegral x)

end IntermediateField

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

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S] (x : S)

-- TODO : move to right place
theorem IsIntegral.adjoin_of_isIntegral [Algebra.IsIntegral R S] (s : Set S) :
    Algebra.IsIntegral R ↥(Algebra.adjoin R s) :=
  (Subalgebra.isIntegral_iff _).mpr (fun x _ ↦ Algebra.IsIntegral.isIntegral x)

section adjoin_eq_top

theorem adjoin_eq_top_iff_aeval_surjective :
    adjoin R {x} = ⊤ ↔ Function.Surjective (aeval x : R[X] →ₐ[R] S) := by
  rw [adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top]

variable {x} (hx : adjoin R {x} = ⊤)

include hx in
theorem aeval_surjective : Function.Surjective (aeval x : R[X] →ₐ[R] S) :=
  (adjoin_eq_top_iff_aeval_surjective _).mp hx

-- TODO : generalise to arbitrary set
include hx in
noncomputable def adjoinEquiv : ↥(adjoin R {x}) ≃ₐ[R] S :=
  (Subalgebra.equivOfEq _ _ hx).trans Subalgebra.topEquiv

theorem adjoinEquiv_apply (y : ↥(adjoin R {x})) : adjoinEquiv hx y = ↑y := rfl

theorem adjoinEquiv_symm_apply (y : S) : (adjoinEquiv hx).symm y = ⟨y, by simp [hx]⟩ := rfl

-- TODO : add version generalised to arbitrary set
include hx in
theorem finite_iff_isIntegral_of_adjoin_eq_top : Module.Finite R S ↔ IsIntegral R x where
  mp _ := _root_.IsIntegral.of_finite R x
  mpr h :=
    have := Algebra.finite_adjoin_simple_of_isIntegral h
    Module.Finite.equiv (adjoinEquiv hx).toLinearEquiv

noncomputable def reprAdjoinEqTop (y : S) : R[X] := (aeval_surjective hx y).choose

@[simp]
theorem aeval_reprAdjoinEqTop (y : S) : aeval x (reprAdjoinEqTop hx y) = y :=
  (aeval_surjective hx y).choose_spec

theorem reprAdjoinEqTop_aeval (f : R[X]) :
    reprAdjoinEqTop hx (aeval x f) - f ∈ RingHom.ker (aeval x) := by simp

include hx in
theorem algHom_ext_of_adjoin_eq_top {S' : Type*} [Semiring S'] [Algebra R S']
    ⦃f g : S →ₐ[R] S'⦄ (h : f x = g x) : f = g := by
  ext y
  rw [← aeval_reprAdjoinEqTop hx y, ← aeval_algHom_apply, ← aeval_algHom_apply, h]

end adjoin_eq_top

theorem adjoin_self_eq_top :
    adjoin R {(⟨x, by aesop⟩ : ↥(adjoin R {x}))} = ⊤ :=
  Subalgebra.map_injective (f := (adjoin R {x}).val) Subtype.val_injective
    (by simp [Subalgebra.range_val])

/-
## Lemmas about *integral* principal generators for an algebra
-/

variable {x}

variable (R x) in
structure IsIntegralUnique : Prop where
  isIntegral : IsIntegral R x
  minpoly_dvd_of_root {f} (hf : aeval x f = 0) : minpoly R x ∣ f

namespace IsIntegralUnique

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

theorem Field.isIntegralUnique {R S : Type*} [Field R] [Ring S] [Algebra R S] {x : R}
    (h₁ : IsIntegral R x) : IsIntegralUnique R x where
  isIntegral := h₁
  minpoly_dvd_of_root := minpoly.dvd R x

theorem IsIntegrallyClosed.isIntegralUnique
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [Algebra R S]
    [IsDomain S] [NoZeroSMulDivisors R S] [IsIntegrallyClosed R] {x : S}
    (h₁ : IsIntegral R x) : IsIntegralUnique R x where
  isIntegral := h₁
  minpoly_dvd_of_root := minpoly.isIntegrallyClosed_dvd h₁

variable (R x) in
structure IsPrimitiveElement : Prop extends IsIntegralUnique R x where
  adjoin_eq_top : adjoin R {x} = ⊤

namespace IsPrimitiveElement

variable (h : IsPrimitiveElement R x)

include h in
theorem algHom_ext {S' : Type*} [Semiring S'] [Algebra R S'] :
    ∀ ⦃f g : S →ₐ[R] S'⦄, f x = g x → f = g := algHom_ext_of_adjoin_eq_top h.adjoin_eq_top

section repr

include h in
theorem modByMonic_reprAdjoinEqTop_aeval (g : R[X]) :
    reprAdjoinEqTop h.adjoin_eq_top (aeval x g) %ₘ minpoly R x = g %ₘ minpoly R x :=
  modByMonic_eq_of_dvd_sub (minpoly.monic h.isIntegral) (h.minpoly_dvd_of_root (by simp))

noncomputable def repr : S →ₗ[R] R[X] where
  toFun y := reprAdjoinEqTop h.adjoin_eq_top y %ₘ minpoly R x
  map_add' y z := by
    rw (occs := [1]) [← aeval_reprAdjoinEqTop h.adjoin_eq_top y,
        ← aeval_reprAdjoinEqTop h.adjoin_eq_top z, ← map_add, modByMonic_reprAdjoinEqTop_aeval h,
        add_modByMonic]
  map_smul' c y := by
    rw (occs := [1]) [RingHom.id_apply, ← aeval_reprAdjoinEqTop h.adjoin_eq_top y, ← map_smul,
        modByMonic_reprAdjoinEqTop_aeval h, ← smul_modByMonic]

@[simp]
theorem aeval_repr (y : S) : aeval x (h.repr y) = y := by
  simp [repr, aeval_modByMonic_minpoly, aeval_reprAdjoinEqTop, *]

@[simp]
theorem repr_aeval (g : R[X]) : h.repr (aeval x g) = g %ₘ minpoly R x :=
  modByMonic_reprAdjoinEqTop_aeval h g

theorem repr_aeval_eq_self_iff [Nontrivial R] (g : R[X]) :
    h.repr (aeval x g) = g ↔ g.degree < (minpoly R x).degree := by
  simpa using modByMonic_eq_self_iff (minpoly.monic h.isIntegral)

theorem repr_aeval_eq_self {g : R[X]} (hg : g.degree < (minpoly R x).degree) :
    h.repr (aeval x g) = g := by
  nontriviality R
  exact (h.repr_aeval_eq_self_iff _).mpr hg

@[simp]
theorem repr_root_pow {n : ℕ} (hdeg : n < (minpoly R x).natDegree) :
    h.repr (x ^ n) = X ^ n := by
  nontriviality R
  rw [← h.repr_aeval_eq_self (g := X ^ n) (by simpa using hdeg)]
  simp

@[simp]
theorem repr_root (hdeg : 1 < (minpoly R x).natDegree) : h.repr x = X := by
  simpa using h.repr_root_pow hdeg

@[simp]
theorem repr_one [Nontrivial S] : h.repr 1 = 1 := by
  simpa using h.repr_root_pow (minpoly.natDegree_pos h.isIntegral)

@[simp]
theorem repr_algebraMap [Nontrivial S] (r : R) :
    h.repr (algebraMap R S r) = algebraMap R R[X] r := by
  simp [Algebra.algebraMap_eq_smul_one, smul_eq_C_mul]

theorem degree_repr_le [Nontrivial R] (y : S) : (h.repr y).degree < (minpoly R x).degree :=
  degree_modByMonic_lt _ (minpoly.monic h.isIntegral)

theorem natDegree_repr_le [Nontrivial S] (y : S) :
    (h.repr y).natDegree < (minpoly R x).natDegree := by
  exact natDegree_modByMonic_lt _ (minpoly.monic h.isIntegral) (minpoly.ne_one R x)

theorem repr_coeff_of_natDegree_le (y : S) {i : ℕ} (hi : (minpoly R x).natDegree ≤ i) :
    (h.repr y).coeff i = 0 := by
  nontriviality R
  exact coeff_eq_zero_of_degree_lt <| (by order [h.degree_repr_le y, degree_le_of_natDegree_le hi])

end repr

section lift

variable {T : Type*} [Ring T] [Algebra R T] {y : T} (hy : aeval y (minpoly R x) = 0)

include hy in
lemma aeval_repr_of_eq_aeval {z : S} (f : R[X]) (hfz : z = aeval x f) :
    aeval y (h.repr z) = aeval y f := by
  simp [hfz, aeval_modByMonic_eq_self_of_root' _ hy]

@[simps! -isSimp apply]
noncomputable def lift : S →ₐ[R] T where
  __ := (aeval y : R[X] →ₐ[R] T) ∘ₗ h.repr
  map_zero' := by simp
  map_one' := by simp [h.aeval_repr_of_eq_aeval hy 1]
  commutes' r := by simp [h.aeval_repr_of_eq_aeval hy (C r)]
  map_mul' a b := by simp [h.aeval_repr_of_eq_aeval hy (h.repr a * h.repr b)]

@[simp]
theorem lift_aeval (f : R[X]) : h.lift hy (aeval x f) = aeval y f := by
  simp [lift_apply, aeval_modByMonic_eq_self_of_root' _ hy]

@[simp]
theorem lift_root : h.lift hy x = y := by simpa using h.lift_aeval hy X

theorem eq_lift {φ : S →ₐ[R] T} (hφ : φ x = y) : φ = h.lift hy := h.algHom_ext (by simp [hφ])

@[simps]
noncomputable def liftEquiv : (S →ₐ[R] T) ≃ { y : T // aeval y (minpoly R x) = 0 } where
  toFun φ := ⟨φ x, by simp⟩
  invFun y := h.lift y.2
  left_inv φ := (h.eq_lift _ (by simp)).symm
  right_inv y := by simp

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
  __ := IsIntegralUnique.of_ker_aeval_eq_span_monic (minpoly.monic h.isIntegral) <| by
    rw [Polynomial.aeval_algEquiv, AlgHom.ker_coe, AlgHom.comp_toRingHom,
        AlgEquiv.coe_ringHom_commutes, ← RingEquiv.toRingHom_eq_coe, RingHom.ker_equiv_comp,
        RingHom.ker_coe_toRingHom, h.ker_aeval]
  adjoin_eq_top := by
    have : (adjoin R {x}).map φ.toAlgHom = ⊤ := by
      simp [h.adjoin_eq_top, AlgHom.range_eq_top, AlgEquiv.surjective]
    simpa [AlgHom.map_adjoin φ.toAlgHom {x}]

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
  h.repr

theorem coeff_apply_of_natDegree_le (z : S) (i : ℕ) (hi : (minpoly R x).natDegree ≤ i) :
    h.coeff z i = 0 := by
  nontriviality R
  simpa [coeff] using h.repr_coeff_of_natDegree_le z hi

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
  { toFun y := (h.repr y).toFinsupp.comapDomain _ Fin.val_injective.injOn
    invFun g := aeval x (ofFinsupp (g.mapDomain Fin.val))
    left_inv y := by
      simp only
      rw [Finsupp.mapDomain_comapDomain _ Fin.val_injective]
      · simp
      · intro i hi
        contrapose! hi
        simpa [toFinsupp_apply] using h.repr_coeff_of_natDegree_le y (by simpa using hi)
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

@[simps! gen dim basis]
noncomputable def powerBasis : PowerBasis R S where
  gen := x
  dim := natDegree (minpoly R x)
  basis := h.basis
  basis_eq_pow := by simp

end basis

-- TODO : particular instances of IsIntegralUnique and IsPrimitiveElement
-- S/R is finite, free, generated by x (IsPrimitiveElement)

theorem _root_.Algebra.adjoin.IsPrimitiveElement (hx : IsIntegralUnique R x) :
    IsPrimitiveElement R (⟨x, by aesop⟩ : ↥(adjoin R {x})) where
  __ := Algebra.adjoin.isIntegralUnique hx
  adjoin_eq_top := adjoin_self_eq_top x

theorem of_powerBasis [Module.Finite R S] (pb : PowerBasis R S) : IsPrimitiveElement R pb.gen where
  adjoin_eq_top := pb.adjoin_gen_eq_top
  isIntegral := pb.isIntegral_gen
  minpoly_dvd_of_root {f} hf := by
    nontriviality R
    nontriviality S
    have : (f %ₘ minpoly R pb.gen).natDegree < pb.dim := by
      simpa using natDegree_modByMonic_lt f
        (minpoly.monic pb.isIntegral_gen) (minpoly.ne_one _ _)
    rw [← modByMonic_eq_zero_iff_dvd (minpoly.monic pb.isIntegral_gen),
        Polynomial.ext_iff_natDegree_le (n := pb.dim - 1) (by omega) (by simp)]
    rw [← aeval_modByMonic_minpoly, ← pb.basis.forall_coord_eq_zero_iff,
        aeval_eq_sum_range' this, Finset.sum_range, Fin.forall_iff] at hf
    simp_rw [← pb.basis_eq_pow, pb.basis.coord_apply, map_sum, map_smul, pb.basis.repr_self] at hf
    simpa [Finsupp.single_eq_pi_single, ← Nat.le_pred_iff_lt pb.dim_pos] using hf

theorem of_free [Module.Finite R S] [Module.Free R S] (adjoin_eq_top : adjoin R {x} = ⊤) :
    IsPrimitiveElement R x where
  adjoin_eq_top := adjoin_eq_top
  isIntegral := by rw [← finite_iff_isIntegral_of_adjoin_eq_top adjoin_eq_top]; assumption
  minpoly_dvd_of_root h := by
    nontriviality R
    have basis := Module.Free.chooseBasis R S
    sorry
    -- TODO : prove that a spanning set of size `finrank R S` forms a basis, and apply to the set
    --        `1, x, x ^ 2, ..., x ^ (d - 1)`

end Algebra.IsPrimitiveElement
