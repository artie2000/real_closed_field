/-
Copyright (c) 2024 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.FormallyReal
import RealClosedField.RingOrdering.Order
import RealClosedField.RingOrdering.Adjoin

variable {F : Type*} [Field F]

/- TODO : upstream global instance -/
instance [LinearOrder F] [IsOrderedRing F] : IsStrictOrderedRing F :=
  IsOrderedRing.toIsStrictOrderedRing F

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

variable (F) in
open Classical RingPreordering in
noncomputable abbrev LinearOrder.mkOfIsSemireal [IsSemireal F] : LinearOrder F :=
  have := (choose_spec <| exists_le_isPrimeOrdering (⊥ : RingPreordering F)).2
  mkOfRingOrdering_field (choose <| exists_le_isPrimeOrdering ⊥)

lemma IsOrderedRing.mkOfIsSemireal [IsSemireal F] :
    letI _ := LinearOrder.mkOfIsSemireal F
    IsOrderedRing F := .mkOfRingPreordering _

theorem Field.exists_isOrderedRing_iff_isSemireal :
    (∃ l : LinearOrder F, IsOrderedRing F) ↔ IsSemireal F :=
  ⟨fun ⟨_, _⟩ => inferInstance, fun _ => ⟨.mkOfIsSemireal _, .mkOfIsSemireal⟩⟩

lemma IsSemireal.existsUnique_isOrderedRing
    [IsSemireal F] (h : ∀ x : F, IsSumSq x ∨ IsSumSq (-x)) :
    ∃! l : LinearOrder F, IsOrderedRing F := by
  refine ⟨RingOrdering_LinearOrder_equiv_field (F := F) ⟨⊥, ⟨by simpa using h⟩⟩, ?_, fun l hl => ?_⟩
  · generalize_proofs p
    exact (RingOrdering_LinearOrder_equiv_field ⟨_, p⟩).property
  · generalize_proofs
    have : IsOrderedRing F := hl
    ext x y
    suffices x ≤ y ↔ IsSumSq (y - x) by simp [this]
    refine ⟨fun hxy => ?_, fun hxy => by linarith [IsSumSq.nonneg hxy]⟩
    · cases h (y - x) with | inl => assumption | inr h =>
      have : x = y := by linarith [IsSumSq.nonneg h]
      simp_all

/- TODO : move to right place -/
lemma Equiv.Subtype.exists_congr {α β : Type*} {p : α → Prop} {q : β → Prop}
    (e : {a // p a} ≃ {b // q b}) : (∃ a, p a) ↔ ∃ b, q b := by
  simp [← nonempty_subtype, Equiv.nonempty_congr e]

/- TODO : move to right place -/
lemma Equiv.Subtype.existsUnique_congr {α β : Type*} {p : α → Prop} {q : β → Prop}
    (e : {a // p a} ≃ {b // q b}) : (∃! a, p a) ↔ ∃! b, q b := by
  simp [← unique_subtype_iff_existsUnique, unique_iff_subsingleton_and_nonempty,
        Equiv.nonempty_congr e, Equiv.subsingleton_congr e]

open RingPreordering in
lemma IsSemireal.isSumSq_or_isSumSq_neg [IsSemireal F]
    (h : ∃! l : LinearOrder F, IsOrderedRing F) :
    ∀ x : F, IsSumSq x ∨ IsSumSq (-x) := by
  rw [Equiv.Subtype.existsUnique_congr RingOrdering_LinearOrder_equiv_field.symm] at h
  by_contra! hc
  rcases hc with ⟨x, hx, hnx⟩
  have : IsSumSq (0 : F) := by aesop
  rcases exists_le_isPrimeOrdering <| adjoin (P := ⊥) (a := x) <|
    minus_one_not_mem_adjoin_linear (by simp_all) with ⟨O₁, hle₁, hO₁⟩
  rcases exists_le_isPrimeOrdering <| adjoin (P := ⊥) (a := -x) <|
    minus_one_not_mem_adjoin_linear (by simp_all)  with ⟨O₂, hle₂, hO₂⟩
  have x_mem : x ∈ O₁ := hle₁ (by aesop)
  apply show O₁ ≠ O₂ from fun h => show x ≠ 0 by aesop <|
      RingPreordering.eq_zero_of_mem_of_neg_mem (show x ∈ O₂ by aesop) (hle₂ (by aesop))
  exact h.unique inferInstance inferInstance

lemma IsSemireal.existsUnique_isOrderedRing_iff [IsSemireal F] :
    (∃! l : LinearOrder F, IsOrderedRing F) ↔ ∀ x : F, IsSumSq x ∨ IsSumSq (-x) :=
  ⟨IsSemireal.isSumSq_or_isSumSq_neg, IsSemireal.existsUnique_isOrderedRing⟩

lemma LinearOrderedField.unique_isOrderedRing_iff [LinearOrder F] [IsOrderedRing F] :
    (∃! l : LinearOrder F, IsOrderedRing F) ↔ ∀ x : F, 0 ≤ x → IsSumSq x := by
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
