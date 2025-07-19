/-
Copyright (c) 2024 Artie Khovanov. All rights reserved.
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

/- TODO : decide whether to unify these -/
instance (O : RingPreordering F) [O.IsOrdering] : IsMaxCone O where
  mem_or_neg_mem' := RingPreordering.mem_or_neg_mem O

open Classical in
instance [IsSemireal F] : IsFormallyReal F where
  eq_zero_of_mul_self_add {a} {s} hs h := by
    by_contra
    exact IsSemireal.one_add_ne_zero (by aesop) (show 1 + s * (a⁻¹ * a⁻¹) = 0 by field_simp [h])

open Classical RingPreordering in
theorem Field.exists_isOrderedRing_iff_isSemireal :
    (∃ _ : LinearOrder F, IsOrderedRing F) ↔ IsSemireal F := by
  rw [Equiv.Subtype.exists_congr RingOrdering_IsOrderedRing_equiv_field.symm]
  refine ⟨fun _ => ⟨fun {s} _ h => ?_⟩, fun _ =>
            letI exO := exists_le_isPrimeOrdering (⊥ : RingPreordering F)
            letI inst := (choose_spec exO).2
            ⟨choose exO, inferInstance⟩⟩
  have : s = -1 := by linear_combination h
  aesop

lemma IsSemireal.existsUnique_isOrderedRing
    [IsSemireal F] (h : ∀ x : F, IsSumSq x ∨ IsSumSq (-x)) :
    ∃! _ : LinearOrder F, IsOrderedRing F := by
  let l := RingOrdering_IsOrderedRing_equiv_field (F := F) ⟨⊥, ⟨by simpa using h⟩⟩
  refine ⟨l.val, l.property, fun l' hl' => ?_⟩
  · simp only [l]
    generalize_proofs
    have : IsOrderedRing F := hl' -- for typeclass search
    ext x y
    suffices x ≤ y ↔ IsSumSq (y - x) by simp [this]
    refine ⟨fun hxy => ?_, fun hxy => by linarith [IsSumSq.nonneg hxy]⟩
    · cases h (y - x) with | inl => assumption | inr h =>
      simp_all [show x = y by linarith [IsSumSq.nonneg h]]

open RingPreordering in
lemma IsSemireal.isSumSq_or_isSumSq_neg [IsSemireal F]
    (h : ∃! _ : LinearOrder F, IsOrderedRing F) :
    ∀ x : F, IsSumSq x ∨ IsSumSq (-x) := by
  rw [Equiv.Subtype.existsUnique_congr RingOrdering_IsOrderedRing_equiv_field.symm] at h
  by_contra! hc
  rcases hc with ⟨x, hx, hnx⟩
  rcases exists_le_isPrimeOrdering <| adjoin <| minus_one_not_mem_adjoin_linear
    (by simp_all : -x ∉ ⊥) with ⟨O₁, hle₁, hO₁⟩
  rcases exists_le_isPrimeOrdering <| adjoin <| minus_one_not_mem_adjoin_linear
    (by simp_all : -(-x) ∉ ⊥) with ⟨O₂, hle₂, hO₂⟩
  have x_mem : x ∈ O₁ := hle₁ (by aesop)
  exact (show O₁ ≠ O₂ from fun h => show x ≠ 0 by aesop <|
    RingPreordering.eq_zero_of_mem_of_neg_mem (by simp_all) (hle₂ (by aesop))) <|
      h.unique inferInstance inferInstance

lemma IsSemireal.existsUnique_isOrderedRing_iff [IsSemireal F] :
    (∃! _ : LinearOrder F, IsOrderedRing F) ↔ ∀ x : F, IsSumSq x ∨ IsSumSq (-x) :=
  ⟨IsSemireal.isSumSq_or_isSumSq_neg, IsSemireal.existsUnique_isOrderedRing⟩

lemma LinearOrderedField.unique_isOrderedRing_iff [LinearOrder F] [IsOrderedRing F] :
    (∃! _ : LinearOrder F, IsOrderedRing F) ↔ ∀ x : F, 0 ≤ x → IsSumSq x := by
  rw [IsSemireal.existsUnique_isOrderedRing_iff]
  refine ⟨fun h x hx => ?_, fun h x => ?_⟩
  · cases h x with | inl => assumption | inr ssnx =>
    aesop (add norm (show  x = 0 by linarith [IsSumSq.nonneg ssnx]))
  · by_cases hx : 0 ≤ x
    · simp [h x hx]
    · simp [h (-x) (by linarith)]

noncomputable def Rat.unique_isOrderedRing :
    Unique {l : LinearOrder ℚ // @IsOrderedRing ℚ _ (l.toPartialOrder)} := Classical.choice <| by
  rw [unique_subtype_iff_existsUnique, LinearOrderedField.unique_isOrderedRing_iff]
  refine fun x hx => by
    rw [show x = ∑ i ∈ Finset.range (x.num.toNat * x.den), (1 / (x.den : ℚ)) ^ 2 by
      have : (x * ↑x.den) * ↑x.den = ↑x.num.toNat * ↑x.den := by simp_all; norm_cast; simp_all
      field_simp; ring_nf at *; assumption]
    simp
