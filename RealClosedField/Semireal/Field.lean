/-
Copyright (c) 2024 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.FormallyReal
import RealClosedField.RingOrdering.Order
import RealClosedField.RingOrdering.Adjoin

variable {F : Type*} [Field F]

instance : RingConeClass (RingPreordering F) F where
  eq_zero_of_mem_of_neg_mem {P} {a} ha hna := by
    by_contra h
    have : a⁻¹ * -a ∈ P := by aesop (config := { enableSimp := False })
    aesop

/- TODO : decide whether to unify these -/
instance (O : RingPreordering F) [RingPreordering.IsOrdering O] : IsMaxCone O where
  mem_or_neg_mem' := RingPreordering.mem_or_neg_mem O

instance IsSemireal.instIsFormallyReal [IsSemireal F] : IsFormallyReal F where
  eq_zero_of_mul_self_add {a} {s} hs h := by
    by_contra
    exact one_add_ne_zero (by aesop) (show 1 + s * (a⁻¹ * a⁻¹) = 0 by field_simp [h])

variable [IsSemireal F]

variable (F) in
open Classical RingPreordering in
noncomputable def LinearOrderedField.mkOfIsSemireal [IsSemireal F] : LinearOrderedField F where
  __ := have := (choose_spec <| exists_le_isPrimeOrdering (⊥ : RingPreordering F)).2
        LinearOrderedRing.mkOfCone (choose <| exists_le_isPrimeOrdering ⊥)
  __ := ‹Field F›

theorem ArtinSchreier_basic :
    Nonempty ({S : LinearOrderedField F // S.toField = ‹Field F›}) ↔ IsSemireal F := by
  refine Iff.intro (fun h => ?_) (fun _ => Nonempty.intro ⟨LinearOrderedField.mkOfIsSemireal F, rfl⟩)
  rcases Classical.choice h with ⟨inst, rfl⟩
  infer_instance
