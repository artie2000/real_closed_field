/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import RealClosedField.RingOrdering.Basic
import Mathlib.Algebra.Order.Ring.Cone
import Mathlib.RingTheory.Ideal.Quotient.Operations

abbrev RingPreordering.mkOfCone {R : Type*} [Nontrivial R] [CommRing R] (C : RingCone R)
    [IsMaxCone C] : RingPreordering R where
  __ := RingCone.toSubsemiring C
  isSquare_mem' x := by
    rcases x with ⟨y, rfl⟩
    cases mem_or_neg_mem (C := C) y with
    | inl h  => aesop
    | inr h => simpa using (show -y * -y ∈ C by aesop (config := { enableSimp := false }))
  minus_one_not_mem' h := one_ne_zero <| eq_zero_of_mem_of_neg_mem (one_mem C) h

/-- A maximal cone over a commutative ring `R` is an ordering on `R`. -/
instance {R : Type*} [CommRing R] [Nontrivial R] (C : RingCone R) [IsMaxCone C] :
    RingPreordering.IsOrdering <| RingPreordering.mkOfCone C where
  mem_or_neg_mem' x := mem_or_neg_mem (C := C) x

/- TODO : decide what to do about the maximality typeclasses -/

section CommRing

variable {R : Type*} [CommRing R] {P : RingPreordering R}
    (hP : RingPreordering.AddSubgroup.support P = ⊥)

abbrev RingCone.mkOfRingPreordering : RingCone R where
  __ := P.toSubsemiring
  eq_zero_of_mem_of_neg_mem' {a} := by
    apply_fun (a ∈ ·) at hP
    aesop

instance RingCone.mkOfRingPreordering.inst_isMaxCone [RingPreordering.IsOrdering P] :
    IsMaxCone <| mkOfRingPreordering hP where
  mem_or_neg_mem := RingPreordering.mem_or_neg_mem P

abbrev PartialOrder.mkOfRingPreordering : PartialOrder R :=
  .mkOfAddGroupCone <| RingCone.mkOfRingPreordering hP

abbrev LinearOrder.mkOfRingOrdering [RingPreordering.IsOrdering P] [DecidablePred (· ∈ P)] :
    LinearOrder R :=
  .mkOfAddGroupCone (RingCone.mkOfRingPreordering hP) inferInstance

instance IsOrderedRing.mkOfRingPreordering :
    letI _ : PartialOrder R := .mkOfRingPreordering hP
    IsOrderedRing R :=
  .mkOfCone <| RingCone.mkOfRingPreordering hP

end CommRing

section Field

variable {F : Type*} [Field F] (P : RingPreordering F)

abbrev RingCone.mkOfRingPreordering_field : RingCone F :=
  mkOfRingPreordering <| RingPreordering.support_eq_bot P

abbrev PartialOrder.mkOfRingPreordering_field : PartialOrder F :=
  .mkOfAddGroupCone <| RingCone.mkOfRingPreordering_field P

abbrev LinearOrder.mkOfRingOrdering_field [RingPreordering.IsOrdering P] [DecidablePred (· ∈ P)] :
    LinearOrder F :=
  .mkOfAddGroupCone (RingCone.mkOfRingPreordering_field P) inferInstance

end Field

abbrev RingCone.mkOfRingPreordering_quot {R : Type*} [CommRing R] (P : RingPreordering R)
    [RingPreordering.IsOrdering P] : RingCone (R ⧸ (RingPreordering.Ideal.support P)) := by
  refine mkOfRingPreordering (P := P.map Ideal.Quotient.mk_surjective (by simp)) ?_
  have : Ideal.map (Ideal.Quotient.mk <| RingPreordering.Ideal.support P)
    (RingPreordering.Ideal.support P) = ⊥ := by simp
  ext x
  apply_fun (x ∈ ·) at this
  rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at this
  simp_all
  /- TODO : make this proof better - need theorem like I.map f = f '' ↑I?  -/

/- TODO : move to the right place -/
theorem Quotient.image_mk_eq_lift {α : Type*} {s : Setoid α} (A : Set α)
    (h : ∀ x y, x ≈ y → (x ∈ A ↔ y ∈ A)) :
    (Quotient.mk s) '' A = (Quotient.lift (· ∈ A) (by simpa)) := by
  aesop (add unsafe forward Quotient.exists_rep)

/- TODO : move to the right place -/
@[to_additive]
theorem QuotientGroup.mem_iff_mem_of_rel {G S : Type*} [CommGroup G]
    [SetLike S G] [MulMemClass S G] (H : Subgroup G) {M : S} (hM : (H : Set G) ⊆ M) :
    ∀ x y, QuotientGroup.leftRel H x y → (x ∈ M ↔ y ∈ M) := fun x y hxy => by
  rw [QuotientGroup.leftRel_apply] at hxy
  exact ⟨fun h => by simpa using mul_mem h <| hM hxy,
        fun h => by simpa using mul_mem h <| hM <| inv_mem hxy⟩

/- TODO : move to the right place -/
def decidablePred_mem_map_quotient_mk
    {R S : Type*} [CommRing R] [SetLike S R] [AddMemClass S R] (I : Ideal R)
    {M : S} (hM : (I : Set R) ⊆ M) [DecidablePred (· ∈ M)] :
    DecidablePred (· ∈ (Ideal.Quotient.mk I) '' M) := by
  have : ∀ x y, I.quotientRel x y → (x ∈ M ↔ y ∈ M) :=
    QuotientAddGroup.mem_iff_mem_of_rel _ (by simpa)
  rw [show (· ∈ (Ideal.Quotient.mk I) '' _) = (· ∈ (Quotient.mk _) '' _) by rfl,
      Quotient.image_mk_eq_lift _ this]
  exact Quotient.lift.decidablePred (· ∈ M) (by simpa)

abbrev LinearOrder.mkOfRingPreordering_quot {R : Type*} [CommRing R]
    (P : RingPreordering R) [RingPreordering.IsPrimeOrdering P] [DecidablePred (· ∈ P)] :
    LinearOrder (R ⧸ (RingPreordering.Ideal.support P)) :=
  @mkOfAddGroupCone _ _ _ _ (RingCone.mkOfRingPreordering_quot P) _ _ <| by
    simpa using decidablePred_mem_map_quotient_mk (RingPreordering.Ideal.support P)
      (by aesop (add safe apply Set.sep_subset))

instance IsOrderedRing.mkOfRingPreordering_quot {R : Type*} [CommRing R]
    (P : RingPreordering R) [RingPreordering.IsPrimeOrdering P] [DecidablePred (· ∈ P)] :
    letI  _ : LinearOrder _ := LinearOrder.mkOfRingPreordering_quot P
    IsOrderedRing (R ⧸ (RingPreordering.Ideal.support P)) := mkOfRingPreordering _
