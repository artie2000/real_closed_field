/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import Mathlib.Algebra.Order.Ring.Cone
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
import RealClosedField.Algebra.Order.Ring.Ordering.Basic

/-!

We demonstrate the equivalence of orderings on a commutative ring `R` and
linear ordered quotient domains of `R`. We also specialise to the case where `R` is a field.

## Main results

TODO : come up with the right names
-- equivalence between support-0 orderings and linear ordered ring
-- equivalence between orderings on field and linear ordered field
-- equivalence between orderings and linear ordered quotient domain

## References

- [*An introduction to real algebra*, T.Y. Lam][lam_1984]

-/

-- TODO : upstream following 3 lemmas to Mathlib / gneeralise as needed

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

section CommRing

variable {R : Type*} [Nontrivial R] [CommRing R] (C : RingCone R) [HasMemOrNegMem C]

abbrev RingCone.isPreordering : C.IsPreordering where
  mem_of_isSquare x := by
    rcases x with ⟨y, rfl⟩
    cases mem_or_neg_mem C y with
    | inl h  => aesop
    | inr h => simpa using (show -y * -y ∈ C by aesop (config := { enableSimp := false }))
  neg_one_notMem h := one_ne_zero <| eq_zero_of_mem_of_neg_mem (one_mem C) h

@[simp]
theorem IsPreordering.mkOfCone.support_eq_bot : C.support = ⊥ := by
  aesop (add safe (eq_zero_of_mem_of_neg_mem (C := C)), simp mem_support)

end CommRing

section CommRing

variable {R : Type*} [CommRing R] {P : IsPreordering R} (hP : P.supportAddSubgroup = ⊥)

abbrev RingCone.mkOfIsPreordering : RingCone R where
  __ := P.toSubsemiring
  carrier := P
  eq_zero_of_mem_of_neg_mem' {a} := by
    apply_fun (a ∈ ·) at hP
    aesop (add simp IsPreordering.mem_supportAddSubgroup)

instance [HasMemOrNegMem P] : HasMemOrNegMem <| RingCone.mkOfIsPreordering hP where
  mem_or_neg_mem := mem_or_neg_mem P

abbrev PartialOrder.mkOfIsPreordering : PartialOrder R :=
  .mkOfAddGroupCone <| RingCone.mkOfIsPreordering hP

theorem IsOrderedRing.mkOfIsPreordering :
    letI _ : PartialOrder R := .mkOfIsPreordering hP
    IsOrderedRing R :=
  .mkOfCone <| RingCone.mkOfIsPreordering hP

abbrev LinearOrder.mkOfIsPreordering [HasMemOrNegMem P] [DecidablePred (· ∈ P)] :
    LinearOrder R :=
  .mkOfAddGroupCone (RingCone.mkOfIsPreordering hP)

variable [Nontrivial R]

open Classical
noncomputable def IsPreorderingLinearOrderEquiv :
    Equiv {O : IsPreordering R // ∃ _ : HasMemOrNegMem O, O.supportAddSubgroup = ⊥}
          {l : LinearOrder R // IsOrderedRing R} where
  toFun := fun ⟨_, hO⟩ => ⟨letI _ := hO.1; .mkOfIsPreordering hO.2, .mkOfIsPreordering hO.2⟩
  invFun := fun ⟨_, _⟩ => ⟨.mkOfCone <| .nonneg R, inferInstance, by simp⟩
  left_inv := fun ⟨_, _, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by ext; simp

@[simp]
theorem IsPreorderingLinearOrderEquiv_apply (hP₂ : HasMemOrNegMem P) :
    IsPreorderingLinearOrderEquiv ⟨P, hP₂, hP⟩ = LinearOrder.mkOfIsPreordering hP :=
  rfl

@[simp]
theorem coe_IsPreorderingLinearOrderEquiv_symm_apply
    (l : LinearOrder R) (hl : @IsOrderedRing R _ l.toPartialOrder) :
    IsPreorderingLinearOrderEquiv.symm ⟨l, hl⟩ = (RingCone.nonneg R : Set R) :=
  rfl

@[simp]
theorem mem_IsPreorderingLinearOrderEquiv_symm_apply
    (l : LinearOrder R) (hl : @IsOrderedRing R _ l.toPartialOrder) {x} :
    x ∈ (IsPreorderingLinearOrderEquiv.symm ⟨l, hl⟩ : IsPreordering R) ↔ x ∈ RingCone.nonneg R :=
  .rfl

end CommRing

section Field

variable {F : Type*} [Field F] (P : IsPreordering F)

abbrev RingCone.mkOfIsPreordering_field : RingCone F :=
  mkOfIsPreordering <| IsPreordering.supportAddSubgroup_eq_bot P

instance [P.IsOrdering] : HasMemOrNegMem <| RingCone.mkOfIsPreordering_field P where
  mem_or_neg_mem := mem_or_neg_mem P

abbrev PartialOrder.mkOfIsPreordering_field : PartialOrder F :=
  .mkOfAddGroupCone <| RingCone.mkOfIsPreordering_field P

abbrev LinearOrder.mkOfRingOrdering_field [P.IsOrdering] [DecidablePred (· ∈ P)] :
    LinearOrder F :=
  .mkOfAddGroupCone (RingCone.mkOfIsPreordering_field P)

open Classical in
noncomputable def ringOrderingLinearOrderEquivField :
    Equiv {O : IsPreordering F // O.IsOrdering}
          {l : LinearOrder F // IsStrictOrderedRing F} where
  toFun := fun ⟨O, hO⟩ =>
    let ⟨l, hl⟩ := IsPreorderingLinearOrderEquiv ⟨O, letI _ := hO; inferInstance, by simp⟩
    ⟨l, IsOrderedRing.toIsStrictOrderedRing F⟩
  invFun := fun ⟨l, hl⟩ =>
    let ⟨O, hO⟩ := IsPreorderingLinearOrderEquiv.symm ⟨l, inferInstance⟩
    ⟨O, letI _ := hO.1; .mk⟩
  left_inv := fun ⟨_, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by simp

@[simp]
theorem ringOrderingLinearOrderEquivField_apply (hP : P.IsOrdering) :
    (ringOrderingLinearOrderEquivField ⟨P, hP⟩ : LinearOrder F) =
    IsPreorderingLinearOrderEquiv ⟨P, inferInstance, by simp⟩ := by
  simp [ringOrderingLinearOrderEquivField]

@[simp]
theorem ringOrderingLinearOrderEquivField_symm_apply_coe
    (l : LinearOrder F) (hl : IsStrictOrderedRing F) :
    (ringOrderingLinearOrderEquivField.symm ⟨l, hl⟩ : IsPreordering F) =
    IsPreorderingLinearOrderEquiv.symm ⟨l, inferInstance⟩ := rfl

end Field

section Quot

variable {R : Type*} [CommRing R] (P : IsPreordering R)

abbrev RingCone.mkOfIsPreordering_quot [HasMemOrNegMem P] : RingCone (R ⧸ P.support) := by
  refine mkOfIsPreordering (P := P.map Ideal.Quotient.mk_surjective (by simp)) (by simp)

abbrev PartialOrder.mkOfIsPreordering_quot [HasMemOrNegMem P] :
    PartialOrder (R ⧸ (P.support)) :=
  .mkOfAddGroupCone <| RingCone.mkOfIsPreordering_quot P

theorem IsOrderedRing.mkOfIsPreordering_quot [HasMemOrNegMem P] :
    letI  _ : PartialOrder _ := PartialOrder.mkOfIsPreordering_quot P
    IsOrderedRing (R ⧸ (P.support)) := mkOfIsPreordering _

abbrev LinearOrder.mkOfIsPreordering_quot [HasMemOrNegMem P] [DecidablePred (· ∈ P)] :
    LinearOrder (R ⧸ (P.support)) :=
  have : DecidablePred (· ∈ RingCone.mkOfIsPreordering_quot P) := by
    simpa using decidablePred_mem_map_quotient_mk (P.support)
                  (by simp [IsPreordering.coe_support])
  .mkOfAddGroupCone (RingCone.mkOfIsPreordering_quot P)

open Classical
noncomputable def IsPreorderingLinearOrderEquiv_quot :
    Equiv {O : IsPreordering R // HasMemOrNegMem O}
          {p : (I : Ideal R) × LinearOrder (R ⧸ I) // let ⟨I, l⟩ := p; IsOrderedRing (R ⧸ I)} where
  toFun := fun ⟨O, hO⟩ => ⟨⟨O.support, .mkOfIsPreordering_quot O⟩, .mkOfIsPreordering_quot O⟩
  invFun := fun ⟨⟨I, l⟩, hl⟩ => ⟨sorry, sorry⟩ -- TODO
  left_inv := fun ⟨_, _⟩ => by sorry --ext; simp
  right_inv := fun ⟨_, _⟩ => by sorry --ext; simp

/- TODO : apply and symm_apply simp lemmas -/

end Quot
