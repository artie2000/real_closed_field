/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Order.Ring.Defs
import RealClosedField.RingOrdering.Order
import RealClosedField.RingOrdering.Adjoin
import RealClosedField.Prereqs
import Mathlib.RingTheory.Adjoin.Field
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.KummerExtension

/- An ordered R-algebra is an R-algebra whose algebra map is order-preserving. -/
class IsOrderedAlgebra (R A : Type*) [CommSemiring R] [Semiring A] [LinearOrder R] [LinearOrder A]
    [IsOrderedRing R] [IsOrderedRing A] [Algebra R A] : Prop where
  monotone : Monotone <| algebraMap R A

attribute [mono] IsOrderedAlgebra.monotone

namespace IsOrderedAlgebra
open scoped algebraMap

variable {R A : Type*} [CommSemiring R] [Semiring A] [LinearOrder R] [LinearOrder A]
    [IsOrderedRing R] [IsOrderedRing A] [Algebra R A] [IsOrderedAlgebra R A]

lemma coe_mono {a b : R} (hab : a ≤ b) : (a : A) ≤ (b : A) := IsOrderedAlgebra.monotone hab

end IsOrderedAlgebra

variable {F K : Type*} [Field F] [LinearOrder F] [IsOrderedRing F] [Field K] [Algebra F K]

/- TODO : generalise to extensions of ordered rings -/

open Classical in
open scoped algebraMap in
noncomputable def RingOrdering_IsOrderedAlgebra_equiv_field :
    Equiv {O : RingPreordering K // O.IsOrdering ∧
            Subsemiring.map (algebraMap F K) (Subsemiring.nonneg F) ≤ O.toSubsemiring}
          {l : LinearOrder K // ∃ _ : IsOrderedRing K, IsOrderedAlgebra F K} where
  toFun := fun ⟨O, hO, hO₂⟩ =>
    letI l := (RingOrdering_IsOrderedRing_equiv_field ⟨O, hO⟩).1
    letI hl := (RingOrdering_IsOrderedRing_equiv_field ⟨O, hO⟩).2
    ⟨l, ⟨hl, ⟨by
      rw [monotone_iff_map_nonneg]
      intro a ha
      apply_fun (fun s ↦ s.carrier : Subsemiring K → Set K) at hO₂
      · simp only [Subsemiring.map_toSubmonoid, Subsemiring.coe_nonneg,
          Subsemiring.coe_carrier_toSubmonoid, RingPreordering.coe_toSubsemiring, Set.le_eq_subset,
          Set.image_subset_iff] at hO₂
        simpa [l] using hO₂ ha
      · exact fun _ _ h ↦ h⟩⟩⟩
  invFun := fun ⟨l, hl⟩ =>
    let O := RingOrdering_IsOrderedRing_equiv_field.symm ⟨l, hl.fst⟩
    ⟨O, O.property, fun x hx => by
    rcases hl with ⟨hl, hl₂⟩
    have : ∀ b : F, 0 ≤ b → 0 ≤ (b : K) := fun _ h ↦ by simpa using IsOrderedAlgebra.coe_mono (A := K) h
    aesop⟩
  left_inv := fun ⟨_, _, _⟩ => by ext; simp
  right_inv := fun _ => by ext; simp

@[simp]
theorem RingOrdering_IsOrderedAlgebra_equiv_field_apply_coe
    {O : RingPreordering K} (hO : O.IsOrdering)
    (hO₂ : Subsemiring.map (algebraMap F K) (Subsemiring.nonneg F) ≤ O.toSubsemiring) :
    (RingOrdering_IsOrderedAlgebra_equiv_field ⟨O, hO, hO₂⟩ : LinearOrder K) =
    RingOrdering_IsOrderedRing_equiv_field ⟨O, hO⟩ := rfl

@[simp]
theorem RingOrdering_IsOrderedAlgebra_equiv_field_symm_apply_coe
    (l : LinearOrder K) (hl : IsOrderedRing K) (hl₂ : IsOrderedAlgebra F K) :
    (RingOrdering_IsOrderedAlgebra_equiv_field.symm ⟨l, hl, hl₂⟩ : RingPreordering K) =
    RingOrdering_IsOrderedRing_equiv_field.symm ⟨l, hl⟩ := rfl

open Classical Subsemiring in
theorem Field.exists_isOrderedAlgebra_iff_minus_one_not_mem_sup :
    (∃ l : LinearOrder K, ∃ _ : IsOrderedRing K, IsOrderedAlgebra F K) ↔
    -1 ∉ ((Subsemiring.nonneg F).map (algebraMap F K) ⊔ Subsemiring.sumSq K) := by
  rw [Equiv.Subtype.exists_congr RingOrdering_IsOrderedAlgebra_equiv_field.symm]
  refine ⟨fun ⟨O, hO, hO₂⟩ hc => ?_, fun h => ?_⟩
  · suffices Subsemiring.map (algebraMap F K) (Subsemiring.nonneg F) ⊔ Subsemiring.sumSq K ≤
             O.toSubsemiring from
      RingPreordering.minus_one_not_mem _ <| this hc
    rw [sup_le_iff]
    exact ⟨hO₂, fun _ => by simp_all⟩
  · rcases RingPreordering.exists_le_isPrimeOrdering <| .mkOfSubsemiring
        ((Subsemiring.nonneg F).map (algebraMap F K) ⊔ Subsemiring.sumSq K) (by simp) h with
      ⟨O, hO, hO₂⟩
    refine ⟨O, ⟨inferInstance, ?_⟩⟩
    intro _ hx
    simpa using hO <| le_sup_left (α := Subsemiring K) hx

open scoped Pointwise in
theorem sup_map_nonneg_sumSq_eq_addSubmonoid_closure_set_mul :
    ↑(((Subsemiring.nonneg F).map (algebraMap F K) ⊔ Subsemiring.sumSq K)) =
    (AddSubmonoid.closure <| ((Subsemiring.nonneg F).map (algebraMap F K) : Set K) *
                             (Submonoid.square K : Set K) : Set K) := by
  rw (occs := .pos [1])
     [← Subsemiring.closure_isSquare,
      ← Subsemiring.closure_eq <| (Subsemiring.nonneg F).map (algebraMap F K),
      ← Subsemiring.closure_union,
      ← Subsemiring.closure_submonoid_closure,
      ← Submonoid.subsemiringClosure_eq_closure,
      Submonoid.subsemiringClosure_coe,
      ← Subsemiring.coe_toSubmonoid,
      ← Submonoid.coe_square,
      ← Submonoid.sup_eq_closure,
      Submonoid.coe_sup,
      Subsemiring.coe_toSubmonoid]

open scoped Pointwise in
theorem Field.exists_isOrderedAlgebra_iff_minus_one_not_mem_closure_mul :
    (∃ l : LinearOrder K, ∃ _ : IsOrderedRing K, IsOrderedAlgebra F K) ↔
    -1 ∉ (AddSubmonoid.closure <|
      ((Subsemiring.nonneg F).map (algebraMap F K) : Set K) * (Submonoid.square K : Set K)) := by
  rw [← SetLike.mem_coe, ← sup_map_nonneg_sumSq_eq_addSubmonoid_closure_set_mul, SetLike.mem_coe,
    Field.exists_isOrderedAlgebra_iff_minus_one_not_mem_sup]

open scoped Pointwise algebraMap in
theorem Field.exists_isOrderedAlgebra_of_projection
    (π : K →ₗ[F] F) (hπ : ∀ x, x ≠ 0 → 0 < π (x * x)) :
    (∃ l : LinearOrder K, ∃ _ : IsOrderedRing K, IsOrderedAlgebra F K) := by
  rw [Field.exists_isOrderedAlgebra_iff_minus_one_not_mem_closure_mul]
  have ih : ∀ x ∈ (AddSubmonoid.closure <| ((Subsemiring.nonneg F).map (algebraMap F K) : Set K) *
      (Submonoid.square K : Set K)), 0 ≤ π x := by
    apply AddSubmonoid.closure_induction
    · intro x hx
      rcases Set.mem_mul.mp hx with ⟨_, ⟨c, hc, rfl⟩, _, ⟨d, rfl⟩, rfl⟩
      by_cases hd : d = 0
      · simp [hd]
      · simpa [← Algebra.smul_def] using (mul_nonneg_iff_of_pos_right (hπ d hd)).mpr hc
    · simp
    · intro x y hx hy ihx ihy
      linarith [map_add π x y]
  intro h
  simpa using not_le_of_gt (hπ 1 (by simp)) (by simpa using ih _ h)

open Polynomial in
theorem X_sq_sub_C_irreducible_iff_not_isSquare {F : Type*} [Field F] (a : F) :
    Irreducible (X ^ 2 - C a) ↔ ¬ IsSquare a := by
  rw [isSquare_iff_exists_sq]
  have := X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two (a := a)
  grind

open Polynomial in
theorem adj_sqrt_ordered {a : F} (ha : 0 ≤ a) (ha₂ : ¬ IsSquare a) :
    letI K := AdjoinRoot (X ^ 2 - C a)
    (∃ l : LinearOrder K, ∃ _ : IsOrderedRing K, IsOrderedAlgebra F K) := by
  have : 0 < a := lt_of_le_of_ne ha (by aesop)
  rw [← X_sq_sub_C_irreducible_iff_not_isSquare] at ha₂
  have := Fact.mk ha₂
  set B := AdjoinRoot.powerBasis <| show X ^ 2 - C a ≠ 0 by apply_fun natDegree; simp
  have Bdim : B.dim = 2 := by simp [B]
  have Bgen : B.gen = AdjoinRoot.root (X ^ 2 - C a) := by simp [B]
  rcases B with ⟨α, n, B, hB⟩
  simp only at Bdim Bgen
  revert B
  rw [Bdim, Bgen]
  intro B hB
  refine Field.exists_isOrderedAlgebra_of_projection (Basis.coord B 0) fun x hx => ?_
  rw [← Basis.sum_repr B x]
  simp [hB, Algebra.smul_def, -AdjoinRoot.algebraMap_eq]
  ring_nf
  have : AdjoinRoot.root (X ^ 2 - C a) ^ 2 - algebraMap F _ a = 0 := by
      have := AdjoinRoot.eval₂_root (X ^ 2 - C a)
      simp_all
  rw [show AdjoinRoot.root (X ^ 2 - C a) ^ 2 = algebraMap F _ a by linear_combination this]
  simp [-AdjoinRoot.algebraMap_eq, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one, pow_two]
  rw [show _ * 2 = (2 : F) • AdjoinRoot.root (X ^ 2 - C a) by rw [mul_comm]; norm_cast; simp,
      map_smul,
      show 1 = B 0 by simp [hB],
      show AdjoinRoot.root (X ^ 2 - C a) = B 1 by simp [hB]]
  simp [← pow_two]
  suffices h : B.repr x 0 ≠ 0 ∨ B.repr x 1 ≠ 0 by
    cases h with
    | inl h => linear_combination pow_two_pos_of_ne_zero h + a * (sq_nonneg <| B.repr x 1)
    | inr h => linear_combination (sq_nonneg <| B.repr x 0) + a * (pow_two_pos_of_ne_zero h)
  by_contra h
  exact hx <| (Basis.forall_coord_eq_zero_iff B).mp <| fun i => by fin_cases i <;> simp_all
