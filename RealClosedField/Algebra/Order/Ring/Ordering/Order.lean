/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import Mathlib.Algebra.Order.Ring.Cone
import Mathlib.RingTheory.Ideal.Quotient.Operations
import RealClosedField.Prereqs
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

section CommRing

variable {R : Type*} [Nontrivial R] [CommRing R] (C : RingCone R) [IsMaxCone C]

abbrev RingPreordering.mkOfCone : RingPreordering R where
  __ := C.toSubsemiring
  carrier := C
  mem_of_isSquare' x := by
    rcases x with ⟨y, rfl⟩
    have := mem_or_neg_mem C
    cases mem_or_neg_mem C y with
    | inl h  => aesop
    | inr h => simpa using (show -y * -y ∈ C by aesop (config := { enableSimp := false }))
  neg_one_notMem' h := one_ne_zero <| eq_zero_of_mem_of_neg_mem (one_mem C) h

instance : HasMemOrNegMem (RingPreordering.mkOfCone C) where
  mem_or_neg_mem := mem_or_neg_mem C

@[simp]
theorem RingPreordering.mkOfCone.support_eq_bot : (mkOfCone C).support = ⊥ := by
  aesop (add safe (eq_zero_of_mem_of_neg_mem (C := C)), simp mem_support)

end CommRing

section CommRing

variable {R : Type*} [CommRing R] {P : RingPreordering R} (hP : P.supportAddSubgroup = ⊥)

abbrev RingCone.mkOfRingPreordering : RingCone R where
  __ := P.toSubsemiring
  carrier := P
  eq_zero_of_mem_of_neg_mem' {a} := by
    apply_fun (a ∈ ·) at hP
    aesop (add simp RingPreordering.mem_supportAddSubgroup)

instance [HasMemOrNegMem P] : IsMaxCone <| RingCone.mkOfRingPreordering hP where
  mem_or_neg_mem' := mem_or_neg_mem P

abbrev PartialOrder.mkOfRingPreordering : PartialOrder R :=
  .mkOfAddGroupCone <| RingCone.mkOfRingPreordering hP

theorem IsOrderedRing.mkOfRingPreordering :
    letI _ : PartialOrder R := .mkOfRingPreordering hP
    IsOrderedRing R :=
  .mkOfCone <| RingCone.mkOfRingPreordering hP

abbrev LinearOrder.mkOfRingPreordering [HasMemOrNegMem P] [DecidablePred (· ∈ P)] :
    LinearOrder R :=
  .mkOfAddGroupCone (RingCone.mkOfRingPreordering hP)

variable [Nontrivial R]

open Classical
noncomputable def ringPreorderingLinearOrderEquiv :
    Equiv {O : RingPreordering R // ∃ _ : HasMemOrNegMem O, O.supportAddSubgroup = ⊥}
          {l : LinearOrder R // IsOrderedRing R} where
  toFun := fun ⟨_, hO⟩ => ⟨letI _ := hO.1; .mkOfRingPreordering hO.2, .mkOfRingPreordering hO.2⟩
  invFun := fun ⟨_, _⟩ => ⟨.mkOfCone <| .nonneg R, inferInstance, by simp⟩
  left_inv := fun ⟨_, _, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by ext; simp

@[simp]
theorem ringPreorderingLinearOrderEquiv_apply (hP₂ : HasMemOrNegMem P) :
    ringPreorderingLinearOrderEquiv ⟨P, hP₂, hP⟩ = LinearOrder.mkOfRingPreordering hP :=
  rfl

@[simp]
theorem coe_ringPreorderingLinearOrderEquiv_symm_apply
    (l : LinearOrder R) (hl : @IsOrderedRing R _ l.toPartialOrder) :
    ringPreorderingLinearOrderEquiv.symm ⟨l, hl⟩ = (RingCone.nonneg R : Set R) :=
  rfl

@[simp]
theorem mem_ringPreorderingLinearOrderEquiv_symm_apply
    (l : LinearOrder R) (hl : @IsOrderedRing R _ l.toPartialOrder) {x} :
    x ∈ (ringPreorderingLinearOrderEquiv.symm ⟨l, hl⟩ : RingPreordering R) ↔ x ∈ RingCone.nonneg R :=
  .rfl

end CommRing

section Field

variable {F : Type*} [Field F] (P : RingPreordering F)

abbrev RingCone.mkOfRingPreordering_field : RingCone F :=
  mkOfRingPreordering <| RingPreordering.supportAddSubgroup_eq_bot P

instance [P.IsOrdering] : IsMaxCone <| RingCone.mkOfRingPreordering_field P where
  mem_or_neg_mem' := mem_or_neg_mem P

abbrev PartialOrder.mkOfRingPreordering_field : PartialOrder F :=
  .mkOfAddGroupCone <| RingCone.mkOfRingPreordering_field P

abbrev LinearOrder.mkOfRingOrdering_field [P.IsOrdering] [DecidablePred (· ∈ P)] :
    LinearOrder F :=
  .mkOfAddGroupCone (RingCone.mkOfRingPreordering_field P)

open Classical in
noncomputable def RingOrdering_IsOrderedRing_equiv_field :
    Equiv {O : RingPreordering F // O.IsOrdering}
          {l : LinearOrder F // IsStrictOrderedRing F} where
  toFun := fun ⟨O, hO⟩ =>
    let ⟨l, hl⟩ := ringPreorderingLinearOrderEquiv ⟨O, letI _ := hO; inferInstance, by simp⟩
    ⟨l, IsOrderedRing.toIsStrictOrderedRing F⟩
  invFun := fun ⟨l, hl⟩ =>
    let ⟨O, hO⟩ := ringPreorderingLinearOrderEquiv.symm ⟨l, inferInstance⟩
    ⟨O, letI _ := hO.1; .mk⟩
  left_inv := fun ⟨_, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by simp

@[simp]
theorem RingOrdering_IsOrderedRing_equiv_field_apply (hP : P.IsOrdering) :
    (RingOrdering_IsOrderedRing_equiv_field ⟨P, hP⟩ : LinearOrder F) =
    ringPreorderingLinearOrderEquiv ⟨P, inferInstance, by simp⟩ := by
  simp [RingOrdering_IsOrderedRing_equiv_field]

@[simp]
theorem RingOrdering_IsOrderedRing_equiv_field_symm_apply_coe
    (l : LinearOrder F) (hl : IsStrictOrderedRing F) :
    (RingOrdering_IsOrderedRing_equiv_field.symm ⟨l, hl⟩ : RingPreordering F) =
    ringPreorderingLinearOrderEquiv.symm ⟨l, inferInstance⟩ := rfl

end Field

section Quot

variable {R : Type*} [CommRing R] (P : RingPreordering R)

abbrev RingCone.mkOfRingPreordering_quot [HasMemOrNegMem P] : RingCone (R ⧸ P.support) := by
  refine mkOfRingPreordering (P := P.map Ideal.Quotient.mk_surjective (by simp)) (by simp)

abbrev PartialOrder.mkOfRingPreordering_quot [HasMemOrNegMem P] :
    PartialOrder (R ⧸ (P.support)) :=
  .mkOfAddGroupCone <| RingCone.mkOfRingPreordering_quot P

theorem IsOrderedRing.mkOfRingPreordering_quot [HasMemOrNegMem P] :
    letI  _ : PartialOrder _ := PartialOrder.mkOfRingPreordering_quot P
    IsOrderedRing (R ⧸ (P.support)) := mkOfRingPreordering _

abbrev LinearOrder.mkOfRingPreordering_quot [HasMemOrNegMem P] [DecidablePred (· ∈ P)] :
    LinearOrder (R ⧸ (P.support)) :=
  have : DecidablePred (· ∈ RingCone.mkOfRingPreordering_quot P) := by
    simpa using decidablePred_mem_map_quotient_mk (P.support)
                  (by simp [RingPreordering.coe_support])
  .mkOfAddGroupCone (RingCone.mkOfRingPreordering_quot P)

open Classical
noncomputable def ringPreorderingLinearOrderEquiv_quot :
    Equiv {O : RingPreordering R // HasMemOrNegMem O}
          {p : (I : Ideal R) × LinearOrder (R ⧸ I) // let ⟨I, l⟩ := p; IsOrderedRing (R ⧸ I)} where
  toFun := fun ⟨O, hO⟩ => ⟨⟨O.support, .mkOfRingPreordering_quot O⟩, .mkOfRingPreordering_quot O⟩
  invFun := fun ⟨⟨I, l⟩, hl⟩ => ⟨sorry, sorry⟩ -- TODO
  left_inv := fun ⟨_, _⟩ => by sorry --ext; simp
  right_inv := fun ⟨_, _⟩ => by sorry --ext; simp

/- TODO : apply and symm_apply simp lemmas -/

end Quot
