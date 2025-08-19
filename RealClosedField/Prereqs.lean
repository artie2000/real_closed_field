/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.RingTheory.Ideal.Quotient.Defs

/- Lemmas that should be upstreamed to Mathlib -/

--PR
/-- Typeclass for substructures S such that S ∪ -S = G. -/
class HasMemOrNegMem {S G : Type*} [AddCommGroup G] [SetLike S G] (C : S) : Prop where
  mem_or_neg_mem (C) (a : G) : a ∈ C ∨ -a ∈ C

--PR
export HasMemOrNegMem (mem_or_neg_mem)

--PR
/-- Typeclass for substructures S such that S ∪ S⁻¹ = G. -/
@[to_additive]
class HasMemOrInvMem {S G : Type*} [CommGroup G] [SetLike S G] (C : S) : Prop where
  mem_or_inv_mem (C) (a : G) : a ∈ C ∨ a⁻¹ ∈ C

--PR
export HasMemOrInvMem (mem_or_inv_mem)

theorem Quotient.image_mk_eq_lift {α : Type*} {s : Setoid α} (A : Set α)
    (h : ∀ x y, x ≈ y → (x ∈ A ↔ y ∈ A)) :
    (Quotient.mk s) '' A = (Quotient.lift (· ∈ A) (by simpa)) := by
  aesop (add unsafe forward Quotient.exists_rep)

@[to_additive]
theorem QuotientGroup.mem_iff_mem_of_rel {G S : Type*} [CommGroup G]
    [SetLike S G] [MulMemClass S G] (H : Subgroup G) {M : S} (hM : (H : Set G) ⊆ M) :
    ∀ x y, QuotientGroup.leftRel H x y → (x ∈ M ↔ y ∈ M) := fun x y hxy => by
  rw [QuotientGroup.leftRel_apply] at hxy
  exact ⟨fun h => by simpa using mul_mem h <| hM hxy,
        fun h => by simpa using mul_mem h <| hM <| inv_mem hxy⟩

def decidablePred_mem_map_quotient_mk
    {R S : Type*} [CommRing R] [SetLike S R] [AddMemClass S R] (I : Ideal R)
    {M : S} (hM : (I : Set R) ⊆ M) [DecidablePred (· ∈ M)] :
    DecidablePred (· ∈ (Ideal.Quotient.mk I) '' M) := by
  have : ∀ x y, I.quotientRel x y → (x ∈ M ↔ y ∈ M) :=
    QuotientAddGroup.mem_iff_mem_of_rel _ (by simpa)
  rw [show (· ∈ (Ideal.Quotient.mk I) '' _) = (· ∈ (Quotient.mk _) '' _) by rfl,
      Quotient.image_mk_eq_lift _ this]
  exact Quotient.lift.decidablePred (· ∈ M) (by simpa)

#min_imports
