/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.Algebra.Ring.Subsemiring.Order
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.Quotient.Operations

/- Lemmas that should be upstreamed to Mathlib -/

lemma Equiv.Subtype.exists_congr {α β : Type*} {p : α → Prop} {q : β → Prop}
    (e : {a // p a} ≃ {b // q b}) : (∃ a, p a) ↔ ∃ b, q b := by
  simp [← nonempty_subtype, Equiv.nonempty_congr e]

lemma Equiv.Subtype.existsUnique_congr {α β : Type*} {p : α → Prop} {q : β → Prop}
    (e : {a // p a} ≃ {b // q b}) : (∃! a, p a) ↔ ∃! b, q b := by
  simp [← unique_subtype_iff_existsUnique, unique_iff_subsingleton_and_nonempty,
        Equiv.nonempty_congr e, Equiv.subsingleton_congr e]

theorem Ideal.coe_map_of_surjective {R S F : Type*} [Semiring R] [Semiring S] [FunLike F R S]
    [RingHomClass F R S] {f : F} (hf : Function.Surjective f) {I : Ideal R} :
    map f I = f '' I := by
  ext y
  exact mem_map_iff_of_surjective _ hf

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

instance {F : Type*} [Field F] [LinearOrder F] [IsOrderedRing F] : IsStrictOrderedRing F :=
  IsOrderedRing.toIsStrictOrderedRing F

@[simp]
lemma Subsemiring.mem_nonneg {R : Type u_2} [Semiring R] [PartialOrder R] [IsOrderedRing R] {x : R} :
  x ∈ nonneg R ↔ x ≥ 0 := Iff.rfl
