/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.Algebra.Ring.FormallyReal
import RealClosedField.Algebra.Order.Ring.Ordering.Order
import RealClosedField.Algebra.Order.Ring.Ordering.Adjoin

variable {F : Type*} [Field F]

instance : RingConeClass (RingPreordering F) F where
  eq_zero_of_mem_of_neg_mem {P} {a} ha hna := by
    by_contra
    have : a⁻¹ * -a ∈ P := by aesop (config := { enableSimp := False })
    aesop

open Classical in
def IsSemireal.isFormallyReal [IsSemireal F] : IsFormallyReal F :=
  isFormallyReal_of_eq_zero_of_eq_zero_of_add_mul_self F <| fun {s} {a} _ h ↦ by
    by_contra
    exact IsSemireal.one_add_ne_zero (by aesop) (show 1 + s * (a⁻¹ * a⁻¹) = 0 by field_simp [h])

open Classical RingPreordering in
theorem Field.exists_isStrictOrderedRing_iff_isSemireal :
    (∃ _ : LinearOrder F, IsStrictOrderedRing F) ↔ IsSemireal F := by
  rw [Equiv.exists_subtype_congr ringOrderingLinearOrderEquivField.symm]
  exact ⟨fun ⟨O, hO⟩ => ⟨fun {s} hs h => RingPreordering.neg_one_notMem O <|
            mem_of_isSumSq (by simp_all [show s = -1 by linear_combination h])⟩,
          fun _ =>
            letI exO := exists_le_isOrdering (⊥ : RingPreordering F)
            letI inst := (choose_spec exO).2
            ⟨choose exO, inferInstance⟩⟩

theorem IsSemireal.existsUnique_isStrictOrderedRing
    [IsSemireal F] (h : ∀ x : F, IsSumSq x ∨ IsSumSq (-x)) :
    ∃! _ : LinearOrder F, IsStrictOrderedRing F := by
  let l := ringOrderingLinearOrderEquivField (F := F)
    ⟨⊥, { toHasMemOrNegMem := ⟨by simpa using h⟩, toIsPrime := inferInstance }⟩
  refine ⟨l.val, l.property, fun l' hl' => ?_⟩
  · simp only [l]
    generalize_proofs
    have : IsStrictOrderedRing F := hl' -- for typeclass search
    ext x y
    suffices x ≤ y ↔ IsSumSq (y - x) by simp [this]
    refine ⟨fun hxy => ?_, fun hxy => by linarith [IsSumSq.nonneg hxy]⟩
    · cases h (y - x) with | inl => assumption | inr h =>
      simp_all [show x = y by linarith [IsSumSq.nonneg h]]

open RingPreordering in
theorem IsSemireal.isSumSq_or_isSumSq_neg [IsSemireal F]
    (h : ∃! _ : LinearOrder F, IsStrictOrderedRing F) :
    ∀ x : F, IsSumSq x ∨ IsSumSq (-x) := by
  rw [Equiv.existsUnique_subtype_congr ringOrderingLinearOrderEquivField.symm] at h
  by_contra! hc
  rcases hc with ⟨x, hx, hnx⟩
  rcases exists_le_isOrdering <| adjoin <| neg_one_notMem_adjoin_of_neg_notMem
    (by simp_all : -x ∉ ⊥) with ⟨O₁, hle₁, hO₁⟩
  rcases exists_le_isOrdering <| adjoin <| neg_one_notMem_adjoin_of_neg_notMem
    (by simp_all : -(-x) ∉ ⊥) with ⟨O₂, hle₂, hO₂⟩
  have x_mem : x ∈ O₁ := hle₁ (by aesop)
  exact (show O₁ ≠ O₂ from fun h => show x ≠ 0 by aesop <|
    RingPreordering.eq_zero_of_mem_of_neg_mem (by simp_all) (hle₂ (by aesop))) <|
      h.unique inferInstance inferInstance

theorem IsSemireal.existsUnique_isStrictOrderedRing_iff [IsSemireal F] :
    (∃! _ : LinearOrder F, IsStrictOrderedRing F) ↔ ∀ x : F, IsSumSq x ∨ IsSumSq (-x) :=
  ⟨IsSemireal.isSumSq_or_isSumSq_neg, IsSemireal.existsUnique_isStrictOrderedRing⟩

theorem LinearOrderedField.unique_isStrictOrderedRing_iff [LinearOrder F] [IsStrictOrderedRing F] :
    (∃! _ : LinearOrder F, IsStrictOrderedRing F) ↔ ∀ x : F, 0 ≤ x → IsSumSq x := by
  rw [IsSemireal.existsUnique_isStrictOrderedRing_iff]
  refine ⟨fun h x hx => ?_, fun h x => ?_⟩
  · cases h x with | inl => assumption | inr ssnx =>
    aesop (add norm (show  x = 0 by linarith [IsSumSq.nonneg ssnx]))
  · by_cases hx : 0 ≤ x
    · simp [h x hx]
    · simp [h (-x) (by linarith)]

noncomputable def Rat.unique_isStrictOrderedRing :
    Unique {l : LinearOrder ℚ // @IsStrictOrderedRing ℚ _ (l.toPartialOrder)} :=
  Classical.choice <| by
  rw [unique_subtype_iff_existsUnique, LinearOrderedField.unique_isStrictOrderedRing_iff]
  refine fun x hx => by
    rw [show x = ∑ i ∈ Finset.range (x.num.toNat * x.den), (1 / (x.den : ℚ)) ^ 2 by
      have : (x * ↑x.den) * ↑x.den = ↑x.num.toNat * ↑x.den := by simp_all; norm_cast; simp_all
      field_simp; ring_nf at *; assumption]
    simp
