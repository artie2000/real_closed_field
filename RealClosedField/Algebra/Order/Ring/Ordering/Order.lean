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

-- TODO : move to right place
@[simp]
theorem Subsemiring.nonneg_toAddSubmonoid
    (T : Type*) [Semiring T] [PartialOrder T] [IsOrderedRing T] :
  (Subsemiring.nonneg T).toAddSubmonoid = AddSubmonoid.nonneg T := by ext; simp

-- TODO : move to right place; fix proof
instance {T : Type*} [Ring T] [LinearOrder T] [IsOrderedRing T] :
    (AddSubmonoid.nonneg T).HasMemOrNegMem' where
  mem_or_neg_mem := mem_or_neg_mem (AddGroupCone.nonneg T)

@[simp]
theorem AddSubmonoid.nonneg_supportAddSubgroup_eq_bot
    (T : Type*) [Ring T] [PartialOrder T] [IsOrderedRing T] :
    (nonneg T).supportAddSubgroup = ⊥ := by
  ext
  simp [mem_supportAddSubgroup, ge_antisymm_iff]

instance {T : Type*} [Ring T] [LinearOrder T] [IsOrderedRing T] :
    (AddSubmonoid.nonneg T).HasIdealSupport := by
  have : (Subsemiring.nonneg T).HasMemOrNegMem' := by simp; infer_instance
  simpa using (inferInstance : (Subsemiring.nonneg T).HasIdealSupport)

@[simp]
theorem AddSubmonoid.nonneg_support_eq_bot
    (T : Type*) [Ring T] [LinearOrder T] [IsOrderedRing T] :
    (nonneg T).support = ⊥ := by
  apply_fun Submodule.toAddSubgroup using Submodule.toAddSubgroup_injective
  exact AddSubmonoid.nonneg_supportAddSubgroup_eq_bot T

section CommRing

variable {R : Type*} [CommRing R] (C : RingCone R)

@[simp]
theorem RingCone.supportAddSubgroup_eq_bot : C.supportAddSubgroup = ⊥ := by
  aesop (add safe (eq_zero_of_mem_of_neg_mem (C := C)), simp AddSubmonoid.mem_supportAddSubgroup)

@[simp]
theorem RingCone.support_eq_bot [C.HasIdealSupport] : C.support = ⊥ := by
  aesop (add safe (eq_zero_of_mem_of_neg_mem (C := C)), simp AddSubmonoid.mem_support)

abbrev RingCone.isPreordering [Nontrivial R] [C.HasMemOrNegMem'] : C.IsPreordering :=
  .of_support_eq_bot C.support_eq_bot

abbrev RingCone.isOrdering [IsDomain R] [C.HasMemOrNegMem'] : C.IsOrdering :=
  .of_support_eq_bot C.support_eq_bot

end CommRing

section CommRing

variable {R : Type*} [CommRing R] {P : Subsemiring R}

abbrev RingCone.mkOfSubsemiring (hP : P.supportAddSubgroup = ⊥) : RingCone R where
  __ := P
  eq_zero_of_mem_of_neg_mem' {a} := by
    apply_fun (a ∈ ·) at hP
    aesop (add simp AddSubmonoid.mem_supportAddSubgroup)

abbrev RingCone.mkOfSubsemiring' [P.HasIdealSupport] (hP : P.support = ⊥) : RingCone R :=
  .mkOfSubsemiring (P := P) (by simp [hP])

-- TODO : remove this when `MemOrNegMem` has its definition changed
instance [P.HasMemOrNegMem'] (hP : P.support = ⊥) :
    HasMemOrNegMem (RingCone.mkOfSubsemiring' hP) where
  mem_or_neg_mem := P.mem_or_neg_mem

instance [P.HasMemOrNegMem'] (hP : P.support = ⊥) :
    (RingCone.mkOfSubsemiring' hP).HasMemOrNegMem' where
  mem_or_neg_mem := P.mem_or_neg_mem

abbrev PartialOrder.mkOfSubsemiring (hP : P.supportAddSubgroup = ⊥) : PartialOrder R :=
  .mkOfAddGroupCone <| RingCone.mkOfSubsemiring hP

theorem IsOrderedRing.mkOfSubsemiring (hP : P.supportAddSubgroup = ⊥) :
    letI _ : PartialOrder R := .mkOfSubsemiring hP
    IsOrderedRing R :=
  .mkOfCone <| RingCone.mkOfSubsemiring hP

abbrev LinearOrder.mkOfSubsemiring [P.HasMemOrNegMem'] [DecidablePred (· ∈ P)]
    (hP : P.support = ⊥) : LinearOrder R :=
  .mkOfAddGroupCone <| RingCone.mkOfSubsemiring' hP

open Classical in
noncomputable def subsemiringLinearOrderEquiv :
    Equiv {O : Subsemiring R // ∃ _ : O.HasMemOrNegMem', O.support = ⊥}
          {l : LinearOrder R // IsOrderedRing R} where
  toFun := fun ⟨O, hO⟩ => letI _ := hO.1; ⟨.mkOfSubsemiring hO.2, .mkOfSubsemiring (by simp [hO.2])⟩
  invFun := fun ⟨_, _⟩ => ⟨.nonneg R, by simp; infer_instance, by simp⟩
  left_inv := fun ⟨_, _, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by ext; simp

open Classical in
@[simp]
theorem subsemiringLinearOrderEquiv_apply {hP} :
    subsemiringLinearOrderEquiv ⟨P, hP⟩ = have := hP.1; LinearOrder.mkOfSubsemiring hP.2 := rfl

@[simp]
theorem coe_subsemiringLinearOrderEquiv_symm_apply (l : LinearOrder R) (hl : IsOrderedRing R) :
    subsemiringLinearOrderEquiv.symm ⟨l, hl⟩ = (RingCone.nonneg R : Set R) := rfl

@[simp]
theorem mem_subsemiringLinearOrderEquiv_symm_apply {l : LinearOrder R} {hl : IsOrderedRing R} {x} :
    x ∈ (subsemiringLinearOrderEquiv.symm ⟨l, hl⟩ : Subsemiring R) ↔ x ∈ RingCone.nonneg R := .rfl

end CommRing

section Field

variable {F : Type*} [Field F] (P : Subsemiring F)

abbrev RingCone.mkOfIsPreordering [P.IsPreordering] : RingCone F :=
  .mkOfSubsemiring' <| Subsemiring.IsPreordering.support_eq_bot P

-- TODO : figure out why synthesis of `P.IsOrdering -> P.HasMemOrNegMem'` is slow
set_option synthInstance.maxHeartbeats 30000 in
instance [P.IsOrdering] : (RingCone.mkOfIsPreordering P).HasMemOrNegMem' where
  mem_or_neg_mem := P.mem_or_neg_mem

abbrev PartialOrder.mkOfIsPreordering [P.IsPreordering] : PartialOrder F :=
  .mkOfAddGroupCone <| RingCone.mkOfIsPreordering P

abbrev LinearOrder.mkOfIsPreordering [P.IsOrdering] [DecidablePred (· ∈ P)] :
    LinearOrder F :=
  .mkOfAddGroupCone (RingCone.mkOfIsPreordering P)

open Classical in
noncomputable def ringOrderingLinearOrderEquiv :
    Equiv {O : Subsemiring F // O.IsOrdering}
          {l : LinearOrder F // IsStrictOrderedRing F} where
  toFun := fun ⟨O, hO⟩ =>
    let ⟨l, hl⟩ := subsemiringLinearOrderEquiv ⟨O, letI _ := hO; inferInstance, by simp⟩
    ⟨l, IsOrderedRing.toIsStrictOrderedRing F⟩
  invFun := fun ⟨l, hl⟩ =>
    let ⟨O, hO⟩ := subsemiringLinearOrderEquiv.symm ⟨l, inferInstance⟩
    ⟨O, letI _ := hO.1; .of_support_eq_bot hO.2⟩
  left_inv := fun ⟨_, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by simp

@[simp]
theorem ringOrderingLinearOrderEquiv_apply (hP : P.IsOrdering) :
    (ringOrderingLinearOrderEquiv ⟨P, hP⟩ : LinearOrder F) =
    subsemiringLinearOrderEquiv ⟨P, inferInstance, by simp⟩ := by
  simp [ringOrderingLinearOrderEquiv]

@[simp]
theorem ringOrderingLinearOrderEquiv_symm_apply_val
    (l : LinearOrder F) (hl : IsStrictOrderedRing F) :
    (ringOrderingLinearOrderEquiv.symm ⟨l, hl⟩ : Subsemiring F) =
    subsemiringLinearOrderEquiv.symm ⟨l, inferInstance⟩ := rfl

end Field

section Quot

variable {R : Type*} [CommRing R] (O : Subsemiring R) [O.HasMemOrNegMem']

instance : (O.map (Ideal.Quotient.mk O.support)).HasMemOrNegMem' :=
  AddSubmonoid.HasMemOrNegMem.map O.toAddSubmonoid Ideal.Quotient.mk_surjective

theorem Subsemiring.support_map_mk_support_eq_bot :
    (Subsemiring.map (Ideal.Quotient.mk O.support) O).support = ⊥ := by
  simp [Ideal.Quotient.mk_surjective]

abbrev RingCone.mkOfSubsemiring_quot : RingCone (R ⧸ O.support) :=
  .mkOfSubsemiring' O.support_map_mk_support_eq_bot

abbrev PartialOrder.mkOfSubsemiring_quot :
    PartialOrder (R ⧸ O.support) :=
  .mkOfAddGroupCone <| RingCone.mkOfSubsemiring_quot O

theorem IsOrderedRing.mkOfSubsemiring_quot :
    letI  _ : PartialOrder _ := PartialOrder.mkOfSubsemiring_quot O
    IsOrderedRing (R ⧸ O.support) := .mkOfSubsemiring <| by
      simp [↓AddSubmonoid.supportAddSubgroup_eq, ↓O.support_map_mk_support_eq_bot]

abbrev LinearOrder.mkOfSubsemiring_quot [DecidablePred (· ∈ O)] :
    LinearOrder (R ⧸ O.support) :=
  have : DecidablePred (· ∈ RingCone.mkOfSubsemiring_quot O) := by
    simpa using decidablePred_mem_map_quotient_mk (O.support)
                  (by simp [AddSubmonoid.coe_support])
  .mkOfAddGroupCone <| RingCone.mkOfSubsemiring_quot O

open Classical in
noncomputable def subsemiringLinearOrderEquiv_quot :
    Equiv {O : Subsemiring R // O.HasMemOrNegMem'}
          (Σ I : Ideal R, {p : LinearOrder (R ⧸ I) // IsOrderedRing (R ⧸ I)}) where
  toFun := fun ⟨O, hO⟩ => ⟨O.support, ⟨.mkOfSubsemiring_quot O, .mkOfSubsemiring_quot O⟩⟩
  invFun := fun ⟨I, l, hl⟩ =>
    ⟨(subsemiringLinearOrderEquiv.symm ⟨l, hl⟩).val.comap (Ideal.Quotient.mk I),
    ⟨fun a ↦ by simpa using le_total ..⟩⟩
  left_inv := fun ⟨O, hO⟩ => by
    ext x
    simp [-Subsemiring.mem_map]
    constructor
    · simp
      intro y hy hxy
      rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, Ideal.mk_ker] at hxy
      simpa using add_mem hxy.2 hy
    · aesop
  right_inv := fun ⟨I, l, hl⟩ => by
    refine Sigma.eq ?_ ?_
    · ext; simp [AddSubmonoid.mem_support, ← ge_antisymm_iff, ← RingHom.mem_ker]
    · simp
      apply Subtype.ext
      simp
      sorry -- TODO : fix DTT hell

/- TODO : apply and symm_apply simp lemmas -/

end Quot
