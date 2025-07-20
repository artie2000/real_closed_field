/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import Mathlib.Algebra.Order.Ring.Cone
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

@[simp] theorem RingPreordering.mkOfCone_carrier :
    (RingPreordering.mkOfCone C).carrier = C := rfl

/-- A maximal cone over a nontrivial commutative ring `R` is an ordering on `R`. -/
instance : HasMemOrNegMem (RingPreordering.mkOfCone C) where
  mem_or_neg_mem := mem_or_neg_mem C

@[simp]
theorem RingPreordering.mkOfCone.support :
    supportAddSubgroup (mkOfCone C) = ⊥ := by
  aesop (add safe (eq_zero_of_mem_of_neg_mem (C := C)))

end CommRing

section CommRing

variable {R : Type*} [CommRing R] {P : RingPreordering R}
    (hP : RingPreordering.supportAddSubgroup P = ⊥)

abbrev RingCone.mkOfRingPreordering : RingCone R where
  __ := P.toSubsemiring
  carrier := P
  eq_zero_of_mem_of_neg_mem' {a} := by
    apply_fun (a ∈ ·) at hP
    aesop

@[simp] theorem RingCone.mkOfRingPreordering_carrier :
    (RingCone.mkOfRingPreordering hP).carrier = P := rfl

instance [HasMemOrNegMem P] : IsMaxCone <| RingCone.mkOfRingPreordering hP where
  mem_or_neg_mem' := mem_or_neg_mem P

abbrev PartialOrder.mkOfRingPreordering : PartialOrder R :=
  .mkOfAddGroupCone <| RingCone.mkOfRingPreordering hP

theorem IsOrderedRing.mkOfRingPreordering :
    letI _ : PartialOrder R := .mkOfRingPreordering hP
    IsOrderedRing R :=
  .mkOfCone <| RingCone.mkOfRingPreordering hP

abbrev LinearOrder.mkOfRingOrdering [HasMemOrNegMem P] [DecidablePred (· ∈ P)] :
    LinearOrder R :=
  .mkOfAddGroupCone (RingCone.mkOfRingPreordering hP)

variable [Nontrivial R]

open Classical
noncomputable def RingOrdering_LinearOrder_equiv :
    Equiv {O : RingPreordering R // HasMemOrNegMem O ∧ RingPreordering.supportAddSubgroup O = ⊥}
          {l : LinearOrder R // IsOrderedRing R} where
  toFun := fun ⟨_, _, hO⟩ => ⟨.mkOfRingOrdering hO, .mkOfRingPreordering hO⟩
  invFun := fun ⟨_, _⟩ => ⟨.mkOfCone <| .nonneg R, inferInstance, by simp⟩
  left_inv := fun ⟨_, _, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by ext; simp

@[simp]
theorem RingOrdering_LinearOrder_equiv_apply (hP₂ : HasMemOrNegMem P) :
    RingOrdering_LinearOrder_equiv ⟨P, hP₂, hP⟩ = LinearOrder.mkOfRingOrdering hP :=
  rfl

@[simp]
theorem coe_RingOrdering_LinearOrder_equiv_symm_apply
    (l : LinearOrder R) (hl : @IsOrderedRing R _ l.toPartialOrder) :
    RingOrdering_LinearOrder_equiv.symm ⟨l, hl⟩ = (RingCone.nonneg R : Set R) :=
  rfl

@[simp]
theorem mem_RingOrdering_LinearOrder_equiv_symm_apply
    (l : LinearOrder R) (hl : @IsOrderedRing R _ l.toPartialOrder) {x} :
    x ∈ (RingOrdering_LinearOrder_equiv.symm ⟨l, hl⟩ : RingPreordering R) ↔ x ∈ RingCone.nonneg R :=
  .rfl

end CommRing

section Field

variable {F : Type*} [Field F] (P : RingPreordering F)

abbrev RingCone.mkOfRingPreordering_field : RingCone F :=
  mkOfRingPreordering <| RingPreordering.supportAddSubgroup_eq_bot P

instance [HasMemOrNegMem P] : IsMaxCone <| RingCone.mkOfRingPreordering_field P where
  mem_or_neg_mem' := mem_or_neg_mem P

abbrev PartialOrder.mkOfRingPreordering_field : PartialOrder F :=
  .mkOfAddGroupCone <| RingCone.mkOfRingPreordering_field P

abbrev LinearOrder.mkOfRingOrdering_field [HasMemOrNegMem P] [DecidablePred (· ∈ P)] :
    LinearOrder F :=
  .mkOfAddGroupCone (RingCone.mkOfRingPreordering_field P)

open Classical in
noncomputable def RingOrdering_IsOrderedRing_equiv_field :
    Equiv {O : RingPreordering F // HasMemOrNegMem O}
          {l : LinearOrder F // IsOrderedRing F} where
  toFun := fun x => RingOrdering_LinearOrder_equiv ⟨x.1, x.2, by simp⟩
  invFun := fun y => ⟨(RingOrdering_LinearOrder_equiv.symm ⟨y.1, y.2⟩).1,
                      (RingOrdering_LinearOrder_equiv.symm ⟨y.1, y.2⟩).2.1⟩
  left_inv := fun ⟨_, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by simp

@[simp]
theorem RingOrdering_IsOrderedRing_equiv_field_apply (hP : HasMemOrNegMem P) :
    RingOrdering_IsOrderedRing_equiv_field ⟨P, hP⟩ =
    RingOrdering_LinearOrder_equiv ⟨P, hP, by simp⟩ := by
  simp [RingOrdering_IsOrderedRing_equiv_field]

@[simp]
theorem RingOrdering_IsOrderedRing_equiv_field_symm_apply_coe
    (l : LinearOrder F) (hl : IsOrderedRing F) :
    (RingOrdering_IsOrderedRing_equiv_field.symm ⟨l, hl⟩ : RingPreordering F) =
    RingOrdering_LinearOrder_equiv.symm ⟨l, hl⟩ := rfl

end Field

abbrev RingCone.mkOfRingPreordering_quot {R : Type*} [CommRing R] (P : RingPreordering R)
    [HasMemOrNegMem P] : RingCone (R ⧸ RingPreordering.support P) := by
  refine mkOfRingPreordering (P := P.map Ideal.Quotient.mk_surjective (by simp)) ?_
  ext x
  simp only [↓RingPreordering.mem_map_supportAddSubgroup, AddSubgroup.mem_bot]
  apply_fun SetLike.coe using SetLike.coe_injective
  have : _ = (Ideal.Quotient.mk (RingPreordering.support P)) ''
      (RingPreordering.support P) :=
    Ideal.coe_map_of_surjective Ideal.Quotient.mk_surjective
  simp_all

abbrev PartialOrder.mkOfRingPreordering_quot {R : Type*} [CommRing R]
    (P : RingPreordering R) [P.IsOrdering] [DecidablePred (· ∈ P)] :
    PartialOrder (R ⧸ (RingPreordering.support P)) :=
  have : DecidablePred (· ∈ (Ideal.Quotient.mk (RingPreordering.support P) '' P)) := by
    simpa using decidablePred_mem_map_quotient_mk (RingPreordering.support P)
      (by aesop (add safe apply Set.sep_subset))
  .mkOfAddGroupCone <| RingCone.mkOfRingPreordering_quot P

theorem IsOrderedRing.mkOfRingPreordering_quot {R : Type*} [CommRing R]
    (P : RingPreordering R) [P.IsOrdering] [DecidablePred (· ∈ P)] :
    letI  _ : PartialOrder _ := PartialOrder.mkOfRingPreordering_quot P
    IsOrderedRing (R ⧸ (RingPreordering.support P)) := mkOfRingPreordering _

/- TODO : full equivalence between ring orderings and linear ordered quotient domains -/
