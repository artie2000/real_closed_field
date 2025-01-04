/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import RealClosedField.RealClosedField.RingOrdering.Basic
import RealClosedField.Mathlib.Algebra.Order.Ring.Cone

@[reducible]
def RingPreordering.mkOfCone {R : Type*} [Nontrivial R] [CommRing R] (C : RingCone R) [IsMaxCone C] :
    RingPreordering R where
  __ := RingCone.toSubsemiring C
  isSquare_mem' x := by
    rcases x with ⟨y, rfl⟩
    cases mem_or_neg_mem C y with
    | inl h  => aesop
    | inr h => simpa using (show -y * -y ∈ C by aesop (config := { enableSimp := false }))
  minus_one_not_mem' h := one_ne_zero <| RingCone.eq_zero_of_mem_of_neg_mem (one_mem _) h

/-- A maximal cone over a commutative ring `R` is an ordering on `R`. -/
instance {R : Type*} [CommRing R] [Nontrivial R] (C : RingCone R) [IsMaxCone C] :
    RingPreordering.IsOrdering <| RingPreordering.mkOfCone C where
  mem_or_neg_mem' x := mem_or_neg_mem C x

/- TODO : decide what to do about the maximality typeclasses -/

@[reducible] def RingCone.mkOfRingPreordering {R : Type*} [CommRing R] {P : RingPreordering R}
    (hP : RingPreordering.AddSubgroup.support P = ⊥) : RingCone R where
  __ := P.toSubsemiring
  eq_zero_of_mem_of_neg_mem' {a} := by
    have : ∀ x, x ∈ RingPreordering.AddSubgroup.support P → x ∈ (⊥ : AddSubgroup R) := by simp_all
    rcases hP with -
    aesop
  /- TODO : make this proof less awful -/

instance RingCone.mkOfRingPreordering.inst_isMaxCone {R : Type*} [CommRing R]
    {P : RingPreordering R} [RingPreordering.IsOrdering P]
    (hP : RingPreordering.AddSubgroup.support P = ⊥) : IsMaxCone <| mkOfRingPreordering hP where
  mem_or_neg_mem' := RingPreordering.mem_or_neg_mem P

@[reducible] def LinearOrderedRing.mkOfRingOrdering {R : Type*} [CommRing R] [IsDomain R]
    {P : RingPreordering R} [RingPreordering.IsOrdering P] [DecidablePred (· ∈ P)]
    (hP : RingPreordering.AddSubgroup.support P = ⊥) : LinearOrderedRing R :=
  mkOfCone <| RingCone.mkOfRingPreordering hP

@[reducible] def RingCone.mkOfRingPreordering_field {F : Type*} [Field F] (P : RingPreordering F) :
    RingCone F := mkOfRingPreordering <| RingPreordering.support_eq_bot P

@[reducible] def LinearOrderedRing.mkOfRingPreordering_field {F : Type*} [Field F]
    (P : RingPreordering F) [DecidablePred (· ∈ P)] [RingPreordering.IsOrdering P] :
    LinearOrderedRing F :=
  mkOfCone <| RingCone.mkOfRingPreordering_field P

@[reducible] def RingCone.mkOfRingPreordering_quot {R : Type*} [CommRing R] (P : RingPreordering R)
    [RingPreordering.IsOrdering P] : RingCone (R ⧸ (RingPreordering.Ideal.support P)) := by
  refine mkOfRingPreordering (P := P.map Ideal.Quotient.mk_surjective (by simp)) ?_
  have : Ideal.map (Ideal.Quotient.mk <| RingPreordering.Ideal.support P)
    (RingPreordering.Ideal.support P) = ⊥ := by simp
  ext x
  apply_fun (x ∈ ·) at this
  rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at this
  simp_all
  /- TODO : make this proof better -/

/- TODO : move to the right place -/
theorem Quotient.image_mk_eq_lift {α : Type*} {s : Setoid α} (A : Set α)
    (h : ∀ x y, x ≈ y → (x ∈ A ↔ y ∈ A)) :
    (Quotient.mk s) '' A = (Quotient.lift (· ∈ A) (by simpa)) := by
  aesop (add unsafe forward Quotient.exists_rep)

/- TODO : move to the right place -/
@[to_additive]
theorem QuotientGroup.mem_iff_mem_of_quotientRel {G : Type*} [CommGroup G] {H : Subgroup G}
    {M : Submonoid G} (hM : (H : Set G) ⊆ M) :
    ∀ x y, QuotientGroup.leftRel H x y → (x ∈ M ↔ y ∈ M) := fun x y hxy => by
  rw [QuotientGroup.leftRel_apply] at hxy
  exact ⟨fun h => by have := mul_mem h <| hM hxy; simpa,
        fun h => by have := mul_mem h <| hM <| inv_mem hxy; simpa⟩

@[reducible] def LinearOrderedRing.mkOfRingPreordering_quot {R : Type*} [CommRing R]
    (P : RingPreordering R) [RingPreordering.IsPrimeOrdering P] [DecidablePred (· ∈ P)] :
    LinearOrderedRing (R ⧸ (RingPreordering.Ideal.support P)) :=
  /- technical instance -/
  /- TODO : generalise this quotient instance? -/
  have : DecidablePred (· ∈ RingCone.mkOfRingPreordering_quot P) := by
    rw [show (· ∈ RingCone.mkOfRingPreordering_quot P) = (· ∈ (Quotient.mk _) '' P) by rfl]
    have : ∀ x y, (RingPreordering.Ideal.support P).quotientRel x y → (x ∈ P ↔ y ∈ P) :=
      QuotientAddGroup.mem_iff_mem_of_quotientRel
        (M := P.toAddSubmonoid) (H := (RingPreordering.Ideal.support P).toAddSubgroup)
        (by aesop (add unsafe apply Set.sep_subset))
    rw [Quotient.image_mk_eq_lift _ this]
    exact Quotient.lift.decidablePred (· ∈ P) (by simpa)
  mkOfCone (RingCone.mkOfRingPreordering_quot P)
