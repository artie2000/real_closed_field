/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Cone
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Henselian

/- Lemmas that should be upstreamed to Mathlib -/

-- PR
lemma Equiv.Subtype.exists_congr {α β : Type*} {p : α → Prop} {q : β → Prop}
    (e : {a // p a} ≃ {b // q b}) : (∃ a, p a) ↔ ∃ b, q b := by
  simp [← nonempty_subtype, Equiv.nonempty_congr e]

-- PR
lemma Equiv.Subtype.existsUnique_congr {α β : Type*} {p : α → Prop} {q : β → Prop}
    (e : {a // p a} ≃ {b // q b}) : (∃! a, p a) ↔ ∃! b, q b := by
  simp [← unique_subtype_iff_existsUnique, unique_iff_subsingleton_and_nonempty,
        Equiv.nonempty_congr e, Equiv.subsingleton_congr e]

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

-- PR
instance {F : Type*} [Field F] [LinearOrder F] [IsOrderedRing F] : IsStrictOrderedRing F :=
  IsOrderedRing.toIsStrictOrderedRing F

-- PR
open scoped Pointwise in
@[to_additive]
theorem Submonoid.coe_sup {M : Type*} [CommMonoid M] (s t : Submonoid M) :
    ↑(s ⊔ t) = (s : Set M) * (t : Set M) := by
  ext x
  simp [Submonoid.mem_sup, Set.mem_mul]

-- PR
@[simp]
lemma Subsemiring.mem_nonneg {R : Type u_2} [Semiring R] [PartialOrder R] [IsOrderedRing R] {x : R} :
  x ∈ nonneg R ↔ x ≥ 0 := Iff.rfl

-- PR
@[to_additive (attr := simp)]
lemma PartialOrder.mkOfGroupCone_toLE {S G : Type*} [CommGroup G] [SetLike S G]
    [GroupConeClass S G] (C : S) (a b : G) :
    (mkOfGroupCone C).le a b ↔ b / a ∈ C := .rfl

-- PR
@[simp]
theorem Subsemiring.mem_mk {R : Type*} [Ring R] {toSubmonoid : Submonoid R}
    (add_mem) (zero_mem) {x : R} : x ∈ mk toSubmonoid add_mem zero_mem ↔ x ∈ toSubmonoid := .rfl

-- PR
@[simp]
theorem Subsemiring.coe_set_mk {R : Type*} [Ring R] {toSubmonoid : Submonoid R}
    (add_mem) (zero_mem) : (mk toSubmonoid add_mem zero_mem : Set R) = toSubmonoid := rfl

-- PR
@[simp]
theorem RingCone.mem_mk {R : Type*} [Ring R] {toSubsemiring : Subsemiring R}
    (eq_zero_of_mem_of_neg_mem) {x : R} :
    x ∈ mk toSubsemiring eq_zero_of_mem_of_neg_mem ↔ x ∈ toSubsemiring := .rfl

-- PR
@[simp]
theorem RingCone.coe_set_mk {R : Type*} [Ring R] {toSubsemiring : Subsemiring R}
    (eq_zero_of_mem_of_neg_mem) :
    (mk toSubsemiring eq_zero_of_mem_of_neg_mem : Set R) = toSubsemiring := rfl

section equivAdjoin

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
open scoped IntermediateField

lemma Algebra.adjoin_primitiveElement_eq_top {α : E} (hα : F⟮α⟯ = ⊤) :
    adjoin F {α} = ⊤ := by
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_integral (_root_.IsIntegral.of_finite F _),
      hα, IntermediateField.top_toSubalgebra]

open scoped IntermediateField
noncomputable def Field.equivAdjoinRootMinpolyPrimitiveElement {α : E} (hα : F⟮α⟯ = ⊤) :
    AdjoinRoot (minpoly F α) ≃ₐ[F] E :=
  (minpoly.equivAdjoin <| IsIntegral.of_finite ..).trans <|
  (Subalgebra.equivOfEq _ _ <| Algebra.adjoin_primitiveElement_eq_top hα).trans
  Subalgebra.topEquiv

/- TODO : fix bad simps lemmas to match AdjoinRoot.Minpoly.toAdjoin_apply' -/
lemma foo {α : E} (hα : F⟮α⟯ = ⊤) :
    Field.equivAdjoinRootMinpolyPrimitiveElement hα (AdjoinRoot.root _) = α := by
  rw [Field.equivAdjoinRootMinpolyPrimitiveElement]
  simp only [AlgEquiv.trans_apply, Subalgebra.equivOfEq_apply,
    Subalgebra.topEquiv_apply, minpoly.equivAdjoin, AlgEquiv.ofBijective, RingEquiv.ofBijective,
    Equiv.ofBijective, RingHom.coe_coe, AlgEquiv.coe_mk, Equiv.coe_fn_mk,
    AdjoinRoot.Minpoly.toAdjoin_apply']
  simp

end equivAdjoin

#min_imports
