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
instance (O : RingPreordering F) [O.IsOrdering] : IsMaxCone O where
  mem_or_neg_mem := RingPreordering.mem_or_neg_mem O

instance IsSemireal.instIsFormallyReal [IsSemireal F] : IsFormallyReal F where
  eq_zero_of_mul_self_add {a} {s} hs h := by
    by_contra
    exact one_add_ne_zero (by aesop) (show 1 + s * (a⁻¹ * a⁻¹) = 0 by field_simp [h])

variable (F) in
open Classical RingPreordering in
noncomputable abbrev LinearOrder.mkOfIsSemireal [IsSemireal F] : LinearOrder F :=
  have := (choose_spec <| exists_le_isPrimeOrdering (⊥ : RingPreordering F)).2
  LinearOrder.mkOfAddGroupCone (choose <| exists_le_isPrimeOrdering ⊥) inferInstance

lemma IsOrderedRing.mkOfIsSemireal [IsSemireal F] :
    letI _ := LinearOrder.mkOfIsSemireal F
    IsOrderedRing F := .mkOfCone _

theorem ArtinSchreier_basic :
    Nonempty ({O : LinearOrder F // IsOrderedRing F}) ↔ IsSemireal F :=
  Iff.intro
    (fun h => let ⟨_, _⟩ := Classical.choice h
              letI _ := IsOrderedRing.toIsStrictOrderedRing F /- TODO : upstream global instance -/
              inferInstance)
    (fun _ => Nonempty.intro ⟨.mkOfIsSemireal _, .mkOfIsSemireal⟩)
