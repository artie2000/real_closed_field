/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Cone
import Mathlib.Algebra.Ring.SumsOfSquares
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Adjoin.Field
import Mathlib.RingTheory.Henselian

/- Lemmas that should be upstreamed to Mathlib -/

-- merged
theorem Equiv.Subtype.exists_congr {α β : Type*} {p : α → Prop} {q : β → Prop}
    (e : {a // p a} ≃ {b // q b}) : (∃ a, p a) ↔ ∃ b, q b := by
  simp [← nonempty_subtype, Equiv.nonempty_congr e]

-- merged
theorem Equiv.Subtype.existsUnique_congr {α β : Type*} {p : α → Prop} {q : β → Prop}
    (e : {a // p a} ≃ {b // q b}) : (∃! a, p a) ↔ ∃! b, q b := by
  simp [← unique_subtype_iff_existsUnique, unique_iff_subsingleton_and_nonempty,
        Equiv.nonempty_congr e, Equiv.subsingleton_congr e]

-- PR
instance {F : Type*} [Field F] [LinearOrder F] [IsOrderedRing F] : IsStrictOrderedRing F :=
  IsOrderedRing.toIsStrictOrderedRing F

section equivAdjoin

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
open scoped IntermediateField

-- PR
theorem Algebra.adjoin_eq_top_of_intermediateField {S : Set E} (hS : ∀ x ∈ S, IsAlgebraic F x)
    (hS₂ : IntermediateField.adjoin F S = ⊤) : Algebra.adjoin F S = ⊤ := by
  simp [*, ← IntermediateField.adjoin_algebraic_toSubalgebra hS]

-- PR
theorem Algebra.adjoin_eq_top_of_primitive_element {α : E} (hα : IsIntegral F α)
    (hα₂ : F⟮α⟯ = ⊤) : Algebra.adjoin F {α} = ⊤ :=
  Algebra.adjoin_eq_top_of_intermediateField (by simpa [isAlgebraic_iff_isIntegral]) hα₂

-- PR
noncomputable def AlgEquiv.adjoinRootMinpolyPrimitiveElement {α : E}
    (hα : IsIntegral F α) (hα₂ : F⟮α⟯ = ⊤) : AdjoinRoot (minpoly F α) ≃ₐ[F] E :=
  (AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly F α).symm.trans <|
  (Subalgebra.equivOfEq _ _ <| Algebra.adjoin_eq_top_of_primitive_element hα hα₂).trans
  Subalgebra.topEquiv

-- PR
@[simp]
theorem AlgEquiv.adjoinRootMinpolyPrimitiveElement_apply {α : E}
    (hα : IsIntegral F α) (hα₂ : F⟮α⟯ = ⊤) (x) :
    adjoinRootMinpolyPrimitiveElement hα hα₂ x = AdjoinRoot.Minpoly.toAdjoin F α x := rfl

end equivAdjoin

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

namespace Subsemiring

variable {R S : Type*} [NonUnitalNonAssocSemiring R] [HasDistribNeg R]
  [SetLike S R] [NonUnitalSubsemiringClass S R] {s : S}

-- PR
@[aesop unsafe 80% (rule_sets := [SetLike])]
theorem neg_mul_mem {x y : R} (hx : -x ∈ s) (hy : y ∈ s) : -(x * y) ∈ s := by
  simpa using mul_mem hx hy


-- PR
@[aesop unsafe 80% (rule_sets := [SetLike])]
theorem mul_neg_mem {x y : R} (hx : x ∈ s) (hy : -y ∈ s) : -(x * y) ∈ s := by
  simpa using mul_mem hx hy

end Subsemiring

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
