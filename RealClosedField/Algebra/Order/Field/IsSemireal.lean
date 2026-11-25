/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.Algebra.Order.Ring.Ordering.Extend
import RealClosedField.PrimitiveElement.Quadratic

variable {F : Type*} [Field F]

open Classical in
theorem Field.exists_isOrderedRing_iff_isSemireal :
    (∃ _ : LinearOrder F, IsOrderedRing F) ↔ IsSemireal F := by
  rw [Equiv.exists_subtype_congr (isOrderingLinearOrderEquiv F).symm,
    ← exists_isPreordering_iff_isSemireal]
  exact ⟨fun ⟨_, hO⟩ ↦ ⟨_, hO.isPreordering⟩,
    fun ⟨_, hP⟩ ↦ by grind [hP.exists_le_isOrdering]⟩

variable (F) in
@[instance_reducible]
noncomputable def LinearOrder.ofIsSemireal [IsSemireal F] : LinearOrder F :=
  (Field.exists_isOrderedRing_iff_isSemireal.mpr inferInstance).choose

variable (F) in
instance IsOrderedRing.ofIsSemireal [IsSemireal F] :
    letI := LinearOrder.ofIsSemireal F
    IsOrderedRing F :=
  (Field.exists_isOrderedRing_iff_isSemireal.mpr inferInstance).choose_spec

@[instance_reducible]
noncomputable def IsSemireal.unique_isOrderedRing [IsSemireal F]
    (h : ∀ x : F, IsSumSq x ∨ IsSumSq (-x)) :
    Unique {_l : LinearOrder F // IsOrderedRing F} where
  default := Field.isOrderingLinearOrderEquiv F
    ⟨Subsemiring.sumSq F, .of_isSpanning_of_isPointed
      (Subsemiring.IsPreordering.sumSq F).isPointed (by simpa [AddSubmonoid.IsSpanning] using h)⟩
  uniq l' := by
    rcases l' with ⟨l', hl'⟩
    generalize_proofs
    ext x y
    simp +instances [Equiv.subtypeEquivRight_apply] -- TODO : make `Equiv.subtypeEquivRight_apply` a `simp` lemma
    refine ⟨fun _ ↦ ?_, fun hxy ↦ by grind [hxy.nonneg]⟩
    · rcases h (y - x) with h | h
      · exact h
      · simp [show x = y by linarith [h.nonneg]]

theorem IsSemireal.isSumSq_or_isSumSq_neg [IsSemireal F]
    (h : ∃! _ : LinearOrder F, IsOrderedRing F) :
    ∀ x : F, IsSumSq x ∨ IsSumSq (-x) := by
  rw [Equiv.existsUnique_subtype_congr (Field.isOrderingLinearOrderEquiv F).symm] at h
  by_contra! hc
  rcases hc with ⟨x, _⟩
  rcases (Subsemiring.IsPreordering.sumSq F).exists_le_isOrdering_and_mem <|
    (Subsemiring.IsPreordering.sumSq F).neg_one_notMem_closure_insert_of_neg_notMem
      (by simp_all : -x ∉ (Subsemiring.sumSq F)) with ⟨O₁, hle₁, hO₁, hx₁⟩
  rcases (Subsemiring.IsPreordering.sumSq F).exists_le_isOrdering_and_mem <|
    (Subsemiring.IsPreordering.sumSq F).neg_one_notMem_closure_insert_of_neg_notMem
      (by simp_all : -(-x) ∉ (Subsemiring.sumSq F)) with ⟨O₂, hle₂, hO₂, hx₂⟩
  exact (show O₁ ≠ O₂ from fun h ↦ show x ≠ 0 by aesop <|
    hO₁.isPreordering.isPointed.eq_zero_of_mem_of_neg_mem hx₁ (by simp_all)) <|
      h.unique hO₁ hO₂

theorem IsSemireal.existsUnique_isOrderedRing_iff [IsSemireal F] :
    (∃! _ : LinearOrder F, IsOrderedRing F) ↔ ∀ x : F, IsSumSq x ∨ IsSumSq (-x) where
  mp := IsSemireal.isSumSq_or_isSumSq_neg
  mpr h := by
    rw [← unique_subtype_iff_existsUnique]
    exact .intro <| IsSemireal.unique_isOrderedRing h

theorem IsOrderedRing.unique_isOrderedRing_iff [LinearOrder F] [IsOrderedRing F] :
    (∃! _ : LinearOrder F, IsOrderedRing F) ↔ ∀ x : F, 0 ≤ x → IsSumSq x := by
  rw [IsSemireal.existsUnique_isOrderedRing_iff]
  refine ⟨fun h x hx => ?_, fun h x ↦ ?_⟩
  · cases h x with | inl => assumption | inr ssnx =>
    aesop (add norm (show  x = 0 by linarith [IsSumSq.nonneg ssnx]))
  · by_cases hx : 0 ≤ x
    · simp [h x hx]
    · simp [h (-x) (by linarith)]

@[instance_reducible]
noncomputable def Rat.unique_isOrderedRing :
    Unique {l : LinearOrder ℚ // @IsOrderedRing ℚ _ (l.toPartialOrder)} where
  default := ⟨inferInstance, inferInstance⟩
  uniq := by
    suffices ∃! l : LinearOrder ℚ, @IsOrderedRing ℚ _ (l.toPartialOrder) from fun ⟨l, hl⟩ ↦
      Subtype.ext <| this.unique hl inferInstance
    rw [IsOrderedRing.unique_isOrderedRing_iff]
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
