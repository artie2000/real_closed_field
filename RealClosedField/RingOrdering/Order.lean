/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import RealClosedField.RingOrdering.Basic
import Mathlib.Algebra.Order.Ring.Cone
import RealClosedField.Prereqs

section CommRing

variable {R : Type*} [Nontrivial R] [CommRing R] (C : RingCone R) [IsMaxCone C]

abbrev RingPreordering.mkOfCone : RingPreordering R where
  __ := C.toSubsemiring
  carrier := C
  isSquare_mem' x := by
    rcases x with ⟨y, rfl⟩
    have := mem_or_neg_mem C
    cases mem_or_neg_mem C y with
    | inl h  => aesop
    | inr h => simpa using (show -y * -y ∈ C by aesop (config := { enableSimp := false }))
  minus_one_not_mem' h := one_ne_zero <| eq_zero_of_mem_of_neg_mem (one_mem C) h

@[simp] lemma RingPreordering.mkOfCone_carrier :
    (RingPreordering.mkOfCone C).carrier = C := rfl

/-- A maximal cone over a nontrivial commutative ring `R` is an ordering on `R`. -/
instance : (RingPreordering.mkOfCone C).IsOrdering where
  mem_or_neg_mem := mem_or_neg_mem C

@[simp]
lemma RingPreordering.mkOfCone.support :
    AddSubgroup.support (mkOfCone C) = ⊥ := by
  aesop (add safe (eq_zero_of_mem_of_neg_mem (C := C)))

end CommRing

/- TODO : decide what to do about the maximality typeclasses -/

section CommRing

variable {R : Type*} [CommRing R] {P : RingPreordering R}
    (hP : RingPreordering.AddSubgroup.support P = ⊥)

abbrev RingCone.mkOfRingPreordering : RingCone R where
  __ := P.toSubsemiring
  carrier := P
  eq_zero_of_mem_of_neg_mem' {a} := by
    apply_fun (a ∈ ·) at hP
    aesop

@[simp] lemma RingCone.mkOfRingPreordering_carrier :
    (RingCone.mkOfRingPreordering hP).carrier = P := rfl

instance [P.IsOrdering] : IsMaxCone <| RingCone.mkOfRingPreordering hP where
  mem_or_neg_mem' := RingPreordering.mem_or_neg_mem P

abbrev PartialOrder.mkOfRingPreordering : PartialOrder R :=
  .mkOfAddGroupCone <| RingCone.mkOfRingPreordering hP

lemma IsOrderedRing.mkOfRingPreordering :
    letI _ : PartialOrder R := .mkOfRingPreordering hP
    IsOrderedRing R :=
  .mkOfCone <| RingCone.mkOfRingPreordering hP

abbrev LinearOrder.mkOfRingOrdering [P.IsOrdering] [DecidablePred (· ∈ P)] :
    LinearOrder R :=
  .mkOfAddGroupCone (RingCone.mkOfRingPreordering hP)

variable [Nontrivial R]

open Classical
noncomputable def RingOrdering_LinearOrder_equiv :
    Equiv {O : RingPreordering R // O.IsOrdering ∧ RingPreordering.AddSubgroup.support O = ⊥}
          {l : LinearOrder R // IsOrderedRing R} where
  toFun := fun ⟨_, _, hO⟩ => ⟨.mkOfRingOrdering hO, .mkOfRingPreordering hO⟩
  invFun := fun ⟨_, _⟩ => ⟨.mkOfCone <| .nonneg R, inferInstance, by simp⟩
  left_inv := fun ⟨_, _, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by ext; simp

@[simp]
theorem RingOrdering_LinearOrder_equiv_apply (hP₂ : P.IsOrdering) :
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
  Iff.rfl

end CommRing

section Field

variable {F : Type*} [Field F] (P : RingPreordering F)

abbrev RingCone.mkOfRingPreordering_field : RingCone F :=
  mkOfRingPreordering <| RingPreordering.support_eq_bot P

instance [P.IsOrdering] : IsMaxCone <| RingCone.mkOfRingPreordering_field P where
  mem_or_neg_mem' := RingPreordering.mem_or_neg_mem P

abbrev PartialOrder.mkOfRingPreordering_field : PartialOrder F :=
  .mkOfAddGroupCone <| RingCone.mkOfRingPreordering_field P

abbrev LinearOrder.mkOfRingOrdering_field [P.IsOrdering] [DecidablePred (· ∈ P)] :
    LinearOrder F :=
  .mkOfAddGroupCone (RingCone.mkOfRingPreordering_field P)

open Classical in
noncomputable def RingOrdering_IsOrderedRing_equiv_field :
    Equiv {O : RingPreordering F // O.IsOrdering}
          {l : LinearOrder F // IsOrderedRing F} where
  toFun := fun x => RingOrdering_LinearOrder_equiv ⟨x.1, x.2, by simp⟩
  invFun := fun y => ⟨(RingOrdering_LinearOrder_equiv.symm ⟨y.1, y.2⟩).1,
                      (RingOrdering_LinearOrder_equiv.symm ⟨y.1, y.2⟩).2.1⟩
  left_inv := fun ⟨_, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by simp

@[simp]
theorem RingOrdering_IsOrderedRing_equiv_field_apply (hP : P.IsOrdering) :
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
    [P.IsOrdering] : RingCone (R ⧸ RingPreordering.Ideal.support P) := by
  refine mkOfRingPreordering (P := P.map Ideal.Quotient.mk_surjective (by simp)) ?_
  apply_fun SetLike.coe using SetLike.coe_injective
  have : _ = (Ideal.Quotient.mk (RingPreordering.Ideal.support P)) ''
      (RingPreordering.Ideal.support P) :=
    Ideal.coe_map_of_surjective Ideal.Quotient.mk_surjective
  simp_all

abbrev PartialOrder.mkOfRingPreordering_quot {R : Type*} [CommRing R]
    (P : RingPreordering R) [P.IsPrimeOrdering] [DecidablePred (· ∈ P)] :
    PartialOrder (R ⧸ (RingPreordering.Ideal.support P)) :=
  have : DecidablePred (· ∈ (Ideal.Quotient.mk (RingPreordering.Ideal.support P) '' P)) := by
    simpa using decidablePred_mem_map_quotient_mk (RingPreordering.Ideal.support P)
      (by aesop (add safe apply Set.sep_subset))
  .mkOfAddGroupCone <| RingCone.mkOfRingPreordering_quot P

lemma IsOrderedRing.mkOfRingPreordering_quot {R : Type*} [CommRing R]
    (P : RingPreordering R) [P.IsPrimeOrdering] [DecidablePred (· ∈ P)] :
    letI  _ : PartialOrder _ := PartialOrder.mkOfRingPreordering_quot P
    IsOrderedRing (R ⧸ (RingPreordering.Ideal.support P)) := mkOfRingPreordering _
