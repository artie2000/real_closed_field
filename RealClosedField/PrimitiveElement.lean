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

section lift

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
theorem repr_root_pow {n : ℕ} (hdeg : n < natDegree (minpoly R x)) :
    h.repr (x ^ n) = X ^ n := by
  nontriviality R
  rw [← h.repr_aeval_eq_self (g := X ^ n) (by simpa using hdeg)]
  simp

@[simp]
theorem repr_root (hdeg : 1 < natDegree (minpoly R x)) : h.repr x = X := by
  simpa using h.repr_root_pow hdeg

theorem degree_repr_le [Nontrivial R] (y : S) : (h.repr y).degree < (minpoly R x).degree :=
  degree_modByMonic_lt _ (minpoly.monic h.isIntegral)

theorem natDegree_repr_le [Nontrivial S] (y : S) :
    (h.repr y).natDegree < (minpoly R x).natDegree := by
  exact natDegree_modByMonic_lt _ (minpoly.monic h.isIntegral) (minpoly.ne_one R x)

theorem repr_coeff (y : S) {i : ℕ} (hi : (minpoly R x).natDegree ≤ i) :
    (h.repr y).coeff i = 0 := by
  nontriviality R
  exact coeff_eq_zero_of_degree_lt <| (h.degree_repr_le y).trans_le (degree_le_of_natDegree_le hi)

end lift

section basis

open Module

noncomputable def coeff : S →ₗ[R] ℕ → R :=
  { toFun := Polynomial.coeff
    map_add' p q := funext (Polynomial.coeff_add p q)
    map_smul' c p := funext (Polynomial.coeff_smul c p) } ∘ₗ
  h.repr

-- TODO : redefine basis in terms of coeff?

noncomputable def basis : Basis (Fin (minpoly R x).natDegree) R S := Basis.ofRepr
  { toFun y := (h.repr y).toFinsupp.comapDomain _ Fin.val_injective.injOn
    invFun g := aeval x (ofFinsupp (g.mapDomain Fin.val))
    left_inv y := by
      simp only
      rw [Finsupp.mapDomain_comapDomain _ Fin.val_injective]
      · simp
      · intro i hi
        suffices i < (minpoly R x).natDegree by simpa
        contrapose! hi
        simpa [Polynomial.toFinsupp_apply] using h.repr_coeff y hi
    right_inv g := by
      nontriviality R
      ext i
      suffices { toFinsupp := Finsupp.mapDomain Fin.val g } %ₘ minpoly R x =
               { toFinsupp := Finsupp.mapDomain Fin.val g } by
        simpa [this] using Finsupp.mapDomain_apply Fin.val_injective ..
      rw [(Polynomial.modByMonic_eq_self_iff (minpoly.monic h.isIntegral)),
          degree_eq_natDegree (minpoly.ne_zero h.isIntegral), degree_lt_iff_coeff_zero]
      intro m hm
      simpa using Finsupp.mapDomain_notin_range _ _ (by simpa)
    map_add' := by simp [Finsupp.comapDomain_add_of_injective Fin.val_injective]
    map_smul' := by simp [Finsupp.comapDomain_smul_of_injective Fin.val_injective] }

@[simp]
theorem basis_apply (i) : h.basis i = x ^ (i : ℕ) := by simp [basis]

theorem basis_one (hdeg : 1 < natDegree (minpoly R x)) : h.basis ⟨1, hdeg⟩ = x := by
  rw [h.basis_apply, Fin.val_mk, pow_one]

include h in
theorem free : Module.Free R S := .of_basis h.basis

include h in
theorem finite : Module.Finite R S := .of_basis h.basis

include h in
theorem finrank [Nontrivial R] : finrank R S = (minpoly R x).natDegree := by
  rw [Module.finrank_eq_card_basis h.basis, Fintype.card_fin]

-- TODO : figure out simp normal form for h.coeff and h.basis.repr

@[simp]
theorem basis_repr (y : S) (i : Fin (natDegree (minpoly R x))) :
    h.basis.repr y i = (h.repr y).coeff (i : ℕ) := by
  simp [basis, toFinsupp_apply]

theorem coeff_apply_coe (z : S) (i : Fin (natDegree (minpoly R x))) :
    h.coeff z i = h.basis.repr z i := by simp [coeff]

theorem coeff_apply_lt (z : S) (i : ℕ) (hi : i < natDegree (minpoly R x)) :
    h.coeff z i = h.basis.repr z ⟨i, hi⟩ := h.coeff_apply_coe z ⟨i, hi⟩

theorem coeff_apply_le (z : S) (i : ℕ) (hi : natDegree (minpoly R x) ≤ i) : h.coeff z i = 0 := by
  nontriviality R
  simpa [coeff] using h.repr_coeff z hi

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
  simp [← h.coeff_root_pow (minpoly.natDegree_pos h.isIntegral)]

@[simp]
theorem coeff_root (hdeg : 1 < natDegree (minpoly R x)) : h.coeff x = Pi.single 1 1 := by
  rw [← h.coeff_root_pow hdeg, pow_one]

@[simp]
theorem coeff_algebraMap [Nontrivial S] (r : R) : h.coeff (algebraMap R S r) = Pi.single 0 r := by
  ext i
  simpa [Algebra.algebraMap_eq_smul_one, Pi.smul_apply] using
    Pi.apply_single (fun _ s ↦ r * s) (by simp) 0 1 i

theorem ext_elem ⦃y z : S⦄ (hyz : ∀ i < natDegree (minpoly R x), h.coeff y i = h.coeff z i) :
    y = z :=
  EquivLike.injective h.basis.equivFun <|
    funext fun i ↦ by
      rw [Basis.equivFun_apply, ← h.coeff_apply_coe, Basis.equivFun_apply, ← h.coeff_apply_coe,
          hyz i i.prop]

theorem ext_elem_iff {y z : S} :
    y = z ↔ ∀ i < natDegree (minpoly R x), h.coeff y i = h.coeff z i :=
  ⟨fun hyz _ _ ↦ hyz ▸ rfl, fun hyz ↦ h.ext_elem hyz⟩

theorem coeff_injective : Function.Injective h.coeff := fun _ _ hyz ↦
  h.ext_elem fun _ _ ↦ hyz ▸ rfl

@[simps! gen dim basis]
noncomputable def powerBasis : PowerBasis R S where
  gen := x
  dim := natDegree (minpoly R x)
  basis := h.basis
  basis_eq_pow := h.basis_apply

end basis

-- TODO : particular instances of IsIntegralUnique and IsPrimitiveElement
-- S = ↑R[x] (IsPrimitiveElement from IsIntegralUnique)
-- S/R is finite, free, generated by x (IsPrimitiveElement)

theorem of_isIntegralUnique_adjoin (hx : IsIntegralUnique R x) :
    IsPrimitiveElement R (⟨x, by aesop⟩ : ↥(adjoin R {x})) := sorry
  --__ := h
  --adjoin_eq_top := adjoin_self_eq_top

theorem of_powerBasis [Module.Finite R S] (pb : PowerBasis R S) :
    IsPrimitiveElement R pb.gen where
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
