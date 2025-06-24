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

theorem Field.nonempty_isOrderedRing_iff_isSemireal :
    Nonempty ({l : LinearOrder F // IsOrderedRing F}) ↔ IsSemireal F :=
  ⟨fun h => let ⟨_, _⟩ := Classical.choice h
            letI _ := IsOrderedRing.toIsStrictOrderedRing F /- TODO : upstream global instance -/
            inferInstance,
   fun _ => Nonempty.intro ⟨.mkOfIsSemireal _, .mkOfIsSemireal⟩⟩

noncomputable def IsSemireal.unique_isOrderedRing
    [IsSemireal F] (h : ∀ x : F, IsSumSq x ∨ IsSumSq (-x)) :
    Unique {l : LinearOrder F // IsOrderedRing F} where
  default := RingOrdering_LinearOrder_equiv_field ⟨⊥, ⟨by simpa using h⟩⟩
  uniq := fun ⟨l, hl⟩ => by
    generalize_proofs
    ext x y
    suffices x ≤ y ↔ IsSumSq (y - x) by simp [this]
    refine ⟨fun hxy => ?_, fun hxy => by linarith [IsSumSq.nonneg hxy]⟩
    · cases h (y - x) with | inl => assumption | inr h =>
      have : x = y := by linarith [IsSumSq.nonneg h]
      simp_all

noncomputable abbrev LinearOrderedField.unique_isOrderedRing
    [LinearOrder F] [IsOrderedRing F] (h : ∀ x : F, x ≥ 0 → IsSumSq x) :
    Unique {l : LinearOrder F // IsOrderedRing F} := IsSemireal.unique_isOrderedRing <| fun x => by
  by_cases hx : x ≥ 0
  · exact Or.inl <| h x hx
  · exact Or.inr <| h (-x) (by linarith)
