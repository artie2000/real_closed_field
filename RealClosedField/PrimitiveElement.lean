/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.PowerBasis
import Mathlib.Algebra.Group.Units.Defs

-- relevant file: Mathlib.RingTheory.Adjoin.PowerBasis

-- TODO : use this file to remove dependency of
--        Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed on AdjoinRoot

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

open Polynomial algebraMap

/-
## Lemmas about principal generators for an algebra
-/

namespace Algebra

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S] (x : S)

theorem adjoin_self_eq_top :
    adjoin R {(⟨x, by aesop⟩ : ↥(adjoin R {x}))} = ⊤ :=
  Subalgebra.map_injective (f := (adjoin R {x}).val) Subtype.val_injective
    (by simp [Subalgebra.range_val])

theorem adjoin_eq_top_iff_aeval_surjective :
    adjoin R {x} = ⊤ ↔ Function.Surjective (aeval x : R[X] →ₐ[R] S) := by
  rw [adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top]

variable {x} (hx : adjoin R {x} = ⊤)

include hx in
theorem aeval_surjective : Function.Surjective (aeval x : R[X] →ₐ[R] S) :=
  (adjoin_eq_top_iff_aeval_surjective _).mp hx

include hx in
noncomputable def adjoinEquiv : ↥(adjoin R {x}) ≃ₐ[R] S :=
  (Subalgebra.equivOfEq _ _ hx).trans Subalgebra.topEquiv

theorem adjoinEquiv_apply (y : ↥(adjoin R {x})) : adjoinEquiv hx y = ↑y := rfl

theorem adjoinEquiv_symm_apply (y : S) : (adjoinEquiv hx).symm y = ⟨y, by simp [hx]⟩ := rfl

noncomputable def repr (y : S) : R[X] := (aeval_surjective hx y).choose

@[simp]
theorem aeval_repr (y : S) : aeval x (repr hx y) = y := (aeval_surjective hx y).choose_spec

theorem repr_aeval (f : R[X]) : repr hx (aeval x f) - f ∈ RingHom.ker (aeval x) := by simp

-- TODO : add version generalised to arbitrary set
include hx in
theorem finite_iff_isIntegral_of_adjoin_eq_top : Module.Finite R S ↔ IsIntegral R x where
  mp _ := _root_.IsIntegral.of_finite R x
  mpr h :=
    have := Algebra.finite_adjoin_simple_of_isIntegral h
    Module.Finite.equiv (adjoinEquiv hx).toLinearEquiv

end Algebra

/-
## Lemmas about *integral* principal generators for an algebra
-/

structure Algebra.IsIntegralUnique (R : Type*) {S : Type*}
    [CommRing R] [Ring S] [Algebra R S] (x : S) : Prop where
  is_integral : IsIntegral R x
  ker_eq_span_minpoly : RingHom.ker (aeval x : _ →ₐ[R] S) = Ideal.span {minpoly R x}

namespace Algebra.IsIntegralUnique

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S] {x : S}

-- TODO : move to right place
theorem eq_of_div_monic {f g : R[X]} (hf : f.Monic) (hg : g.Monic)
    (h₁ : g ∣ f) (h₂ : f.natDegree ≤ g.natDegree) : f = g := by
  by_cases hn : Nontrivial R
  · rcases h₁ with ⟨k, rfl⟩
    have : k ≠ 0 := fun hc ↦ by simp_all
    have : g.leadingCoeff * k.leadingCoeff ≠ 0 := by simp [*]
    rw [natDegree_mul' ‹_›] at h₂
    have : k.Monic := by simpa [leadingCoeff_mul' ‹_›, hg, Monic.def] using hf
    simp [Polynomial.eq_one_of_monic_natDegree_zero this (by omega)]
  · rw [not_nontrivial_iff_subsingleton] at hn
    simp [Subsingleton.eq_zero]

theorem of_ker_aeval_eq_span_monic {g : R[X]} (hg : g.Monic)
    (h : RingHom.ker (aeval x : _→ₐ[R] S) = Ideal.span {g}) : IsIntegralUnique R x :=
  have hi : IsIntegral R x := ⟨g, hg, by simpa [← h] using Ideal.mem_span_singleton_self g⟩
  { is_integral := hi
    ker_eq_span_minpoly := by
      rw [h, eq_of_div_monic (minpoly.monic hi) hg]
      · simp [← Ideal.mem_span_singleton, ← h]
      · exact Polynomial.natDegree_le_natDegree <| minpoly.min R x hg <| by
          simp [← RingHom.mem_ker, h, Ideal.mem_span_singleton_self] }

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
  eq_of_div_monic hmo (minpoly.monic h.is_integral)
    (by simpa [← RingHom.mem_ker, ker_eq_span_minpoly, Ideal.mem_span_singleton, h] using hf)
    (Polynomial.natDegree_le_natDegree fmin)

theorem minpoly_unique (h : IsIntegralUnique R x)
    {f : R[X]} (hmo : f.Monic) (hf : aeval x f = 0)
    (hmin : ∀ g : R[X], g.Monic → aeval x g = 0 → f.degree ≤ g.degree) :
    f = minpoly R x :=
  unique_of_degree_le_degree_minpoly h hmo hf <|
    hmin (minpoly R x) (minpoly.monic h.is_integral) (minpoly.aeval R x)

theorem of_unique_of_degree_le_degree_minpoly
    (is_integral : IsIntegral R x)
    (h : ∀ f : R[X], f.Monic → aeval x f = 0 → f.degree ≤ (minpoly R x).degree → f = minpoly R x) :
    IsIntegralUnique R x where
  is_integral := is_integral
  ker_eq_span_minpoly := by
    by_cases hn : Nontrivial R
    · symm
      refine Submodule.span_eq_of_le _ (by simp) (fun f hf ↦ ?_)
      have := degree_modByMonic_lt f (minpoly.monic is_integral)
      simpa [modByMonic_eq_zero_iff_dvd (minpoly.monic is_integral),
             ← Ideal.mem_span_singleton] using
        h (minpoly R x + f %ₘ minpoly R x)
        (Monic.add_of_left (minpoly.monic is_integral) ‹_›)
        (by simp_all [Polynomial.modByMonic_eq_sub_mul_div _ (minpoly.monic is_integral)])
        (by rw [degree_add_eq_left_of_degree_lt ‹_›])
    · rw [not_nontrivial_iff_subsingleton] at hn
      simp [Subsingleton.elim _ ⊥]

-- TODO : move to right place
theorem Algebra.IsIntegral.adjoin_of_isIntegral [Algebra.IsIntegral R S] (s : Set S) :
    Algebra.IsIntegral R ↥(adjoin R s) :=
  (Subalgebra.isIntegral_iff _).mpr (fun x _ ↦ Algebra.IsIntegral.isIntegral x)

section lift

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {x : S}
         [IsDomain R] [IsDomain S] [NoZeroSMulDivisors R S] [IsIntegrallyClosed R]

-- TODO : move to right place
theorem map_modByMonic (h : IsIntegral R x) (g : R[X]) :
    aeval x (g %ₘ minpoly R x) = aeval x g := by
  rw [← RingHom.sub_mem_ker_iff, ← RingHom.ker_coe_toRingHom,
      ← AlgHom.toRingHom_eq_coe, minpoly.ker_eval h, Ideal.mem_span_singleton,
      modByMonic_eq_sub_mul_div _ (minpoly.monic h), sub_sub_cancel_left, dvd_neg]
  exact dvd_mul_right ..

variable (h : IsIntegralUnique R x)

theorem modByMonic_repr_aeval (g : R[X]) :
    repr h.adjoin_eq_top (aeval x g) %ₘ minpoly R x = g %ₘ minpoly R x :=
  modByMonic_eq_of_dvd_sub (minpoly.monic h.is_integral) <| by
    rw [← Ideal.mem_span_singleton, ← minpoly.ker_eval h.is_integral, RingHom.sub_mem_ker_iff]
    simp

noncomputable def modByMonicHom : S →ₗ[R] R[X] where
  toFun y := repr h.adjoin_eq_top y %ₘ minpoly R x
  map_add' y z := by
    rw (occs := [1]) [← aeval_repr h.adjoin_eq_top y, ← aeval_repr h.adjoin_eq_top z, ← map_add,
          modByMonic_repr_aeval h, add_modByMonic]
  map_smul' c y := by
    rw (occs := [1]) [RingHom.id_apply, ← aeval_repr h.adjoin_eq_top y, ← map_smul,
        modByMonic_repr_aeval h, ← smul_modByMonic]

end lift

end Algebra.IsPrimitiveElem
