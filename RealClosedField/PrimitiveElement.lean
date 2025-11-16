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

-- TODO : move to right place
theorem Polynomial.eq_of_div_monic{R : Type*} [Semiring R] {f g : R[X]}
    (hf : f.Monic) (hg : g.Monic) (h₁ : g ∣ f) (h₂ : f.natDegree ≤ g.natDegree) : f = g := by
  nontriviality R
  rcases h₁ with ⟨k, rfl⟩
  have : k ≠ 0 := fun hc ↦ by simp_all
  have : g.leadingCoeff * k.leadingCoeff ≠ 0 := by simp [*]
  rw [natDegree_mul' ‹_›] at h₂
  have : k.Monic := by simpa [leadingCoeff_mul' ‹_›, hg, Monic.def] using hf
  simp [Polynomial.eq_one_of_monic_natDegree_zero this (by omega)]

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

end adjoin_eq_top

/-
## Lemmas about *integral* principal generators for an algebra
-/

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S] {x : S}

variable (R x) in
structure IsIntegralUnique : Prop where
  is_integral : IsIntegral R x
  ker_aeval : RingHom.ker (aeval x : _ →ₐ[R] S) = Ideal.span {minpoly R x}

namespace IsIntegralUnique

theorem of_ker_aeval_eq_span_monic {g : R[X]} (hg : g.Monic)
    (h : RingHom.ker (aeval x : _→ₐ[R] S) = Ideal.span {g}) : IsIntegralUnique R x :=
  have hi : IsIntegral R x := ⟨g, hg, by simpa [← h] using Ideal.mem_span_singleton_self g⟩
  { is_integral := hi
    ker_aeval := by
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
    (by simpa [← RingHom.mem_ker, ker_aeval, Ideal.mem_span_singleton, h] using hf)
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
  ker_aeval := by
    nontriviality R
    symm
    refine Submodule.span_eq_of_le _ (by simp) (fun f hf ↦ ?_)
    have := degree_modByMonic_lt f (minpoly.monic is_integral)
    simpa [modByMonic_eq_zero_iff_dvd (minpoly.monic is_integral),
            ← Ideal.mem_span_singleton] using
      h (minpoly R x + f %ₘ minpoly R x)
      (Monic.add_of_left (minpoly.monic is_integral) ‹_›)
      (by simp_all [Polynomial.modByMonic_eq_sub_mul_div _ (minpoly.monic is_integral)])
      (by rw [degree_add_eq_left_of_degree_lt ‹_›])

theorem aeval_modByMonic_minpoly (h : IsIntegralUnique R x) (g : R[X]) :
    aeval x (g %ₘ minpoly R x) = aeval x g := by
  rw [← RingHom.sub_mem_ker_iff, h.ker_aeval, Ideal.mem_span_singleton,
      modByMonic_eq_sub_mul_div _ (minpoly.monic h.is_integral), sub_sub_cancel_left, dvd_neg]
  exact dvd_mul_right ..

end IsIntegralUnique

variable (R x) in
structure IsPrimitiveElement : Prop extends IsIntegralUnique R x where
  adjoin_eq_top : adjoin R {x} = ⊤

namespace IsPrimitiveElement

variable (h : IsPrimitiveElement R x)

section lift

include h in
theorem modByMonic_reprAdjoinEqTop_aeval (g : R[X]) :
    reprAdjoinEqTop h.adjoin_eq_top (aeval x g) %ₘ minpoly R x = g %ₘ minpoly R x :=
  modByMonic_eq_of_dvd_sub (minpoly.monic h.is_integral) <| by
    rw [← Ideal.mem_span_singleton, ← h.ker_aeval, RingHom.sub_mem_ker_iff]
    simp

noncomputable def modByMonicHom : S →ₗ[R] R[X] where
  toFun y := reprAdjoinEqTop h.adjoin_eq_top y %ₘ minpoly R x
  map_add' y z := by
    rw (occs := [1]) [← aeval_reprAdjoinEqTop h.adjoin_eq_top y,
        ← aeval_reprAdjoinEqTop h.adjoin_eq_top z, ← map_add, modByMonic_reprAdjoinEqTop_aeval h,
        add_modByMonic]
  map_smul' c y := by
    rw (occs := [1]) [RingHom.id_apply, ← aeval_reprAdjoinEqTop h.adjoin_eq_top y, ← map_smul,
        modByMonic_reprAdjoinEqTop_aeval h, ← smul_modByMonic]

@[simp]
theorem modByMonicHom_aeval (g : R[X]) : h.modByMonicHom (aeval x g) = g %ₘ minpoly R x :=
  modByMonic_reprAdjoinEqTop_aeval h g

@[simp]
theorem aeval_modByMonicHom (y : S) : aeval x (h.modByMonicHom y) = y := by
  simp [modByMonicHom, h.aeval_modByMonic_minpoly, aeval_reprAdjoinEqTop, *]

@[simp]
theorem modByMonicHom_root_pow {n : ℕ} (hdeg : n < natDegree (minpoly R x)) :
    h.modByMonicHom (x ^ n) = X ^ n := by
  nontriviality R
  rw (occs := [2]) [← aeval_X (R := R) x]
  rw [← map_pow, modByMonicHom_aeval, modByMonic_eq_self_iff (minpoly.monic h.is_integral),
      degree_X_pow]
  contrapose! hdeg
  simpa [natDegree_le_iff_degree_le] using hdeg

@[simp]
theorem modByMonicHom_root (hdeg : 1 < natDegree (minpoly R x)) : h.modByMonicHom x = X := by
  simpa using h.modByMonicHom_root_pow hdeg

theorem modByMonicHom_coeff (y : S) {i : ℕ} (hi : (minpoly R x).natDegree ≤ i) :
    (h.modByMonicHom y).coeff i = 0 := by
  nontriviality R
  exact Polynomial.coeff_eq_zero_of_degree_lt <|
    (degree_modByMonic_lt _ (minpoly.monic h.is_integral)).trans_le
      (Polynomial.degree_le_of_natDegree_le hi)

end lift

section basis

open Module

noncomputable def basis : Basis (Fin (natDegree (minpoly R x))) R S := Basis.ofRepr
  { toFun y := (h.modByMonicHom y).toFinsupp.comapDomain _ Fin.val_injective.injOn
    invFun g := aeval x (ofFinsupp (g.mapDomain Fin.val))
    left_inv y := by
      simp only
      rw [Finsupp.mapDomain_comapDomain _ Fin.val_injective]
      · simp
      · intro i hi
        suffices i < (minpoly R x).natDegree by simpa
        contrapose! hi
        simpa [Polynomial.toFinsupp_apply] using h.modByMonicHom_coeff y hi
    right_inv g := by
      nontriviality R
      ext i
      suffices { toFinsupp := Finsupp.mapDomain Fin.val g } %ₘ minpoly R x =
               { toFinsupp := Finsupp.mapDomain Fin.val g } by
        simpa [this] using Finsupp.mapDomain_apply Fin.val_injective ..
      rw [(Polynomial.modByMonic_eq_self_iff (minpoly.monic h.is_integral)),
          degree_eq_natDegree (minpoly.ne_zero h.is_integral), degree_lt_iff_coeff_zero]
      intro m hm
      simpa using Finsupp.mapDomain_notin_range _ _ (by simpa)
    map_add' := by simp [Finsupp.comapDomain_add_of_injective Fin.val_injective]
    map_smul' := by simp [Finsupp.comapDomain_smul_of_injective Fin.val_injective] }

@[simp]
theorem basis_apply (i) : h.basis i = x ^ (i : ℕ) := by simp [basis]

@[simps! gen dim basis]
noncomputable def powerBasis : PowerBasis R S where
  gen := x
  dim := natDegree (minpoly R x)
  basis := h.basis
  basis_eq_pow := h.basis_apply

@[simp]
theorem basis_repr (y : S) (i : Fin (natDegree (minpoly R x))) :
    h.basis.repr y i = (h.modByMonicHom y).coeff (i : ℕ) := by
  simp [basis, toFinsupp_apply]

theorem basis_one (hdeg : 1 < natDegree (minpoly R x)) : h.basis ⟨1, hdeg⟩ = x := by
  rw [h.basis_apply, Fin.val_mk, pow_one]

include h in
theorem finite : Module.Finite R S := h.powerBasis.finite

include h in
theorem finrank [Nontrivial R] : Module.finrank R S = (minpoly R x).natDegree :=
  h.powerBasis.finrank

noncomputable def coeff : S →ₗ[R] ℕ → R :=
  { toFun := Polynomial.coeff
    map_add' p q := funext (Polynomial.coeff_add p q)
    map_smul' c p := funext (Polynomial.coeff_smul c p) } ∘ₗ
  h.modByMonicHom

theorem coeff_apply_lt (z : S) (i : ℕ) (hi : i < natDegree (minpoly R x)) :
    h.coeff z i = h.basis.repr z ⟨i, hi⟩ := by simp [coeff]

theorem coeff_apply_coe (z : S) (i : Fin (natDegree (minpoly R x))) :
    h.coeff z i = h.basis.repr z i := h.coeff_apply_lt ..

theorem coeff_apply_le (z : S) (i : ℕ) (hi : natDegree (minpoly R x) ≤ i) : h.coeff z i = 0 := by
  nontriviality R
  simpa [coeff] using h.modByMonicHom_coeff z hi

theorem coeff_apply (z : S) (i : ℕ) :
    h.coeff z i = if hi : i < natDegree (minpoly R x) then h.basis.repr z ⟨i, hi⟩ else 0 := by
  grind [coeff_apply_lt, coeff_apply_le]

theorem coeff_root_pow {n} (hn : n < natDegree (minpoly R x)) :
    h.coeff (x ^ n) = Pi.single n 1 := by
  ext i
  rw [coeff_apply]
  split_ifs with hi
  · simp [*, Pi.single_apply]
  · grind [Pi.single_eq_of_ne]

@[simp]
theorem coeff_one [Nontrivial S] : h.coeff 1 = Pi.single 0 1 := by
  simp [← h.coeff_root_pow (minpoly.natDegree_pos h.is_integral)]

@[simp]
theorem coeff_root (hdeg : 1 < natDegree (minpoly R x)) : h.coeff x = Pi.single 1 1 := by
  rw [← h.coeff_root_pow hdeg, pow_one]

@[simp]
theorem coeff_algebraMap [Nontrivial S] (r : R) : h.coeff (algebraMap R S r) = Pi.single 0 r := by
  ext i
  simpa [Algebra.algebraMap_eq_smul_one, Pi.smul_apply] using
    Pi.apply_single (fun _ s => r * s) (by simp) 0 1 i

theorem ext_elem ⦃y z : S⦄ (hyz : ∀ i < natDegree (minpoly R x), h.coeff y i = h.coeff z i) :
    y = z :=
  EquivLike.injective h.basis.equivFun <|
    funext fun i => by
      rw [Basis.equivFun_apply, ← h.coeff_apply_coe, Basis.equivFun_apply, ← h.coeff_apply_coe,
          hyz i i.prop]

theorem ext_elem_iff {y z : S} :
    y = z ↔ ∀ i < natDegree (minpoly R x), h.coeff y i = h.coeff z i :=
  ⟨fun hyz _ _=> hyz ▸ rfl, fun hyz => h.ext_elem hyz⟩

theorem coeff_injective : Function.Injective h.coeff := fun _ _ hyz =>
  h.ext_elem fun _ _ => hyz ▸ rfl

end basis

-- TODO : particular isntances of IsPrimitiveElement

end Algebra.IsPrimitiveElement
