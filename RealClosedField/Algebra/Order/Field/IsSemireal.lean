/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.Algebra.Ring.IsSemireal
import RealClosedField.Algebra.Order.Ring.Ordering.Adjoin
import RealClosedField.Algebra.Order.Ring.Ordering.Order
import RealClosedField.PrimitiveElement.Quadratic

variable {F : Type*} [Field F]

open Classical in
theorem Field.exists_isStrictOrderedRing_iff_isSemireal :
    (∃ _ : LinearOrder F, IsStrictOrderedRing F) ↔ IsSemireal F := by
  rw [Equiv.exists_subtype_congr (isOrderingLinearOrderEquiv F).symm]
  exact ⟨fun ⟨O, hO⟩ => ⟨fun {s} hs h => Subsemiring.IsPreordering.neg_one_notMem O <|
            Subsemiring.mem_of_isSumSq O (by simp_all [show s = -1 by linear_combination h])⟩,
          fun _ =>
            letI exO := Subsemiring.IsPreordering.exists_le_isOrdering (Subsemiring.sumSq F)
            letI inst := (choose_spec exO).2
            ⟨choose exO, inferInstance⟩⟩

variable (F) in
noncomputable def LinearOrder.ofIsSemireal [IsSemireal F] : LinearOrder F :=
  (Field.exists_isStrictOrderedRing_iff_isSemireal.mpr inferInstance).choose

variable (F) in
instance IsStrictOrderedRing.ofIsSemireal [IsSemireal F] :
    letI := LinearOrder.ofIsSemireal F
    IsStrictOrderedRing F :=
  (Field.exists_isStrictOrderedRing_iff_isSemireal.mpr inferInstance).choose_spec

noncomputable def IsSemireal.unique_isStrictOrderedRing [IsSemireal F]
    (h : ∀ x : F, IsSumSq x ∨ IsSumSq (-x)) :
    Unique {l : LinearOrder F // IsStrictOrderedRing F} where
  default := Field.isOrderingLinearOrderEquiv F
    ⟨Subsemiring.sumSq F, { toIsSpanning := ⟨by simpa using h⟩, toIsPrime := inferInstance }⟩
  uniq l' := by
    rcases l' with ⟨l', hl'⟩
    generalize_proofs
    ext x y
    suffices x ≤ y ↔ IsSumSq (y - x) by simp [this]
    refine ⟨fun hxy => ?_, fun hxy => by linarith [IsSumSq.nonneg hxy]⟩
    · cases h (y - x) with | inl => assumption | inr h =>
      simp_all [show x = y by linarith [IsSumSq.nonneg h]]

theorem IsSemireal.isSumSq_or_isSumSq_neg [IsSemireal F]
    (h : ∃! _ : LinearOrder F, IsStrictOrderedRing F) :
    ∀ x : F, IsSumSq x ∨ IsSumSq (-x) := by
  rw [Equiv.existsUnique_subtype_congr (Field.isOrderingLinearOrderEquiv F).symm] at h
  by_contra! hc
  rcases hc with ⟨x, _⟩
  rcases Subsemiring.IsPreordering.exists_le_isOrdering_and_mem <|
    Subsemiring.IsPreordering.neg_one_notMem_closure_insert_of_neg_notMem
      (by simp_all : -x ∉ (Subsemiring.sumSq F)) with ⟨O₁, hle₁, hO₁, hx₁⟩
  rcases Subsemiring.IsPreordering.exists_le_isOrdering_and_mem <|
    Subsemiring.IsPreordering.neg_one_notMem_closure_insert_of_neg_notMem
      (by simp_all : -(-x) ∉ (Subsemiring.sumSq F)) with ⟨O₂, hle₂, hO₂, hx₂⟩
  exact (show O₁ ≠ O₂ from fun h => show x ≠ 0 by aesop <|
    O₁.eq_zero_of_mem_of_neg_mem hx₁ (by simp_all)) <|
      h.unique inferInstance inferInstance

theorem IsSemireal.existsUnique_isStrictOrderedRing_iff [IsSemireal F] :
    (∃! _ : LinearOrder F, IsStrictOrderedRing F) ↔ ∀ x : F, IsSumSq x ∨ IsSumSq (-x) where
  mp := IsSemireal.isSumSq_or_isSumSq_neg
  mpr h := by
    rw [← unique_subtype_iff_existsUnique]
    exact .intro <| IsSemireal.unique_isStrictOrderedRing h

theorem IsStrictOrderedRing.unique_isStrictOrderedRing_iff [LinearOrder F] [IsStrictOrderedRing F] :
    (∃! _ : LinearOrder F, IsStrictOrderedRing F) ↔ ∀ x : F, 0 ≤ x → IsSumSq x := by
  rw [IsSemireal.existsUnique_isStrictOrderedRing_iff]
  refine ⟨fun h x hx => ?_, fun h x => ?_⟩
  · cases h x with | inl => assumption | inr ssnx =>
    aesop (add norm (show  x = 0 by linarith [IsSumSq.nonneg ssnx]))
  · by_cases hx : 0 ≤ x
    · simp [h x hx]
    · simp [h (-x) (by linarith)]

noncomputable def Rat.unique_isStrictOrderedRing :
    Unique {l : LinearOrder ℚ // @IsStrictOrderedRing ℚ _ (l.toPartialOrder)} where
  default := ⟨inferInstance, inferInstance⟩
  uniq := by
    suffices ∃! l : LinearOrder ℚ, @IsStrictOrderedRing ℚ _ (l.toPartialOrder) from fun ⟨l, hl⟩ ↦
      Subtype.ext <| this.unique hl inferInstance
    rw [IsStrictOrderedRing.unique_isStrictOrderedRing_iff]
    intro x hx
    rw [show x = ∑ i ∈ Finset.range (x.num.toNat * x.den), (1 / (x.den : ℚ)) ^ 2 by
      simp; field_simp; simp; norm_cast; simpa]
    simp

open Polynomial in
theorem IsSemireal.of_forall_adjoinRoot_i_isSquare {K : Type*} [Field K] [Algebra F K]
    (hK : IsAdjoinRootMonic' K (X ^ 2 + 1 : F[X]))
    (h : ∀ x : K, IsSquare x) : IsSemireal F :=
  .of_not_isSumSq_neg_one fun hc ↦ by
    have hK' : IsIntegralGenSqrt _ (-1 : F) := ⟨by simpa using hK.pe⟩
    exact hK'.not_isSquare <| isSquare_of_isSumSq_of_forall_adjoinRoot_i_isSquare hK h hc
