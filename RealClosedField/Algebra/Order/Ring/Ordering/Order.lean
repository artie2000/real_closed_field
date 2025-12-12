/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import Mathlib.Algebra.Order.Monoid.Submonoid
import Mathlib.Algebra.Ring.Subsemiring.Order
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

-- TODO : upstream the following

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

namespace Submonoid

variable (G : Type*) [CommGroup G]

@[to_additive]
instance [LinearOrder G] [IsOrderedMonoid G] : (oneLE G).HasMemOrInvMem where
  mem_or_inv_mem := by simpa using le_total 1

@[to_additive]
instance [PartialOrder G] [IsOrderedMonoid G] : (oneLE G).IsCone where
  supportSubgroup_eq_bot := by
    ext
    simp [mem_supportSubgroup, ge_antisymm_iff]

end Submonoid

@[simp]
theorem Subsemiring.nonneg_toAddSubmonoid
    (R : Type*) [Semiring R] [PartialOrder R] [IsOrderedRing R] :
  (nonneg R).toAddSubmonoid = AddSubmonoid.nonneg R := by ext; simp

 -- end upstream

section Group

variable {G : Type*} [CommGroup G] (S : Submonoid G) [S.IsCone]

/-- Construct a partial order by designating a cone in an abelian group. -/
@[to_additive /-- Construct a partial order by designating a cone in an abelian group. -/]
abbrev PartialOrder.mkOfSubmonoid : PartialOrder G where
  le a b := b / a ∈ S
  le_refl a := by simp [one_mem]
  le_trans a b c nab nbc := by simpa using mul_mem nbc nab
  le_antisymm a b nab nba := by
    simpa [div_eq_one, eq_comm] using Submonoid.eq_one_of_mem_of_inv_mem nab (by simpa using nba)

@[to_additive (attr := simp)]
lemma PartialOrder.mkOfSubmonoid_le_iff {a b : G} :
    (mkOfSubmonoid S).le a b ↔ b / a ∈ S := Iff.rfl

/-- Construct a partially ordered abelian group by designating a cone in an abelian group. -/
@[to_additive
  /-- Construct a partially ordered abelian group by designating a cone in an abelian group. -/]
lemma IsOrderedMonoid.mkOfSubmonoid :
    letI _ := PartialOrder.mkOfSubmonoid S
    IsOrderedMonoid G :=
  letI _ := PartialOrder.mkOfSubmonoid S
  { mul_le_mul_left := fun a b nab c ↦ by simpa [· ≤ ·] using nab }

/-- Construct a linear order by designating a maximal cone in an abelian group. -/
@[to_additive /-- Construct a linear order by designating a maximal cone in an abelian group. -/]
abbrev LinearOrder.mkOfSubmonoid [S.HasMemOrInvMem] [DecidablePred (· ∈ S)] : LinearOrder G where
  __ := PartialOrder.mkOfSubmonoid S
  le_total a b := by simpa using Submonoid.HasMemOrInvMem.mem_or_inv_mem S (b / a)
  toDecidableLE _ := _

end Group

section Ring

variable {R : Type*} [Ring R] (S : Subsemiring R) [S.IsAddCone]

/-- Construct a partially ordered ring by designating a cone in a ring. -/
lemma IsOrderedRing.mkOfSubsemiring :
    letI _ := PartialOrder.mkOfAddSubmonoid S.toAddSubmonoid
    IsOrderedRing R :=
  letI _ := PartialOrder.mkOfAddSubmonoid S.toAddSubmonoid
  haveI := IsOrderedAddMonoid.mkOfAddSubmonoid S.toAddSubmonoid
  haveI : ZeroLEOneClass R := ⟨by simp⟩
  .of_mul_nonneg fun x y xnn ynn ↦ show _ ∈ S by simpa using Subsemiring.mul_mem _ xnn ynn

end Ring

section CommRing

variable (R : Type*) [CommRing R]

open Classical in
noncomputable def isAddConeLinearOrderEquiv :
    Equiv {C : Subsemiring R // C.IsAddCone ∧ C.HasMemOrNegMem}
          {l : LinearOrder R // IsOrderedRing R} where
  toFun := fun ⟨C, _, _⟩ => ⟨.mkOfAddSubmonoid C.toAddSubmonoid, .mkOfSubsemiring C⟩
  invFun := fun ⟨_, _⟩ => ⟨.nonneg R, by simp; infer_instance, by simp; infer_instance⟩
  left_inv := fun ⟨_, _, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by ext; simp

open Classical in
@[simp]
theorem isAddConeLinearOrderEquiv_apply
    {C : Subsemiring R} {h₁ : C.IsAddCone} {h₂ : C.HasMemOrNegMem} :
    isAddConeLinearOrderEquiv R ⟨C, h₁, h₂⟩ = LinearOrder.mkOfAddSubmonoid C.toAddSubmonoid := rfl

@[simp]
theorem isAddConeLinearOrderEquiv_symm_apply {l : LinearOrder R} {hl : IsOrderedRing R} :
    (isAddConeLinearOrderEquiv R).symm ⟨l, hl⟩ = Subsemiring.nonneg R := rfl

end CommRing

section Field

variable {F : Type*} [Field F]

open Classical in
noncomputable def ringOrderingLinearOrderEquiv :
    Equiv {O : Subsemiring F // O.IsOrdering}
          {l : LinearOrder F // IsStrictOrderedRing F} where
  toFun := fun ⟨O, hO⟩ =>
    let ⟨l, hl⟩ := isAddConeLinearOrderEquiv F ⟨O, inferInstance, inferInstance⟩
    ⟨l, IsOrderedRing.toIsStrictOrderedRing F⟩
  invFun := fun ⟨l, hl⟩ =>
    let ⟨O, h₁, h₂⟩ := (isAddConeLinearOrderEquiv F).symm ⟨l, inferInstance⟩
    ⟨O, inferInstance⟩
  left_inv := fun ⟨_, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by simp

@[simp]
theorem ringOrderingLinearOrderEquiv_apply (hP : P.IsOrdering) :
    (ringOrderingLinearOrderEquiv ⟨P, hP⟩ : LinearOrder F) =
    isAddConeLinearOrderEquiv ⟨P, inferInstance, by simp⟩ := by
  simp [ringOrderingLinearOrderEquiv]

@[simp]
theorem ringOrderingLinearOrderEquiv_symm_apply_val
    (l : LinearOrder F) (hl : IsStrictOrderedRing F) :
    (ringOrderingLinearOrderEquiv.symm ⟨l, hl⟩ : Subsemiring F) =
    isAddConeLinearOrderEquiv.symm ⟨l, inferInstance⟩ := rfl

end Field

section Quot

variable {R : Type*} [CommRing R] (O : Subsemiring R) [O.HasMemOrNegMem]

instance : (O.map (Ideal.Quotient.mk O.support)).HasMemOrNegMem :=
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
noncomputable def isAddConeLinearOrderEquiv_quot :
    Equiv {O : Subsemiring R // O.HasMemOrNegMem}
          (Σ I : Ideal R, {p : LinearOrder (R ⧸ I) // IsOrderedRing (R ⧸ I)}) where
  toFun := fun ⟨O, hO⟩ => ⟨O.support, ⟨.mkOfSubsemiring_quot O, .mkOfSubsemiring_quot O⟩⟩
  invFun := fun ⟨I, l, hl⟩ =>
    ⟨(isAddConeLinearOrderEquiv.symm ⟨l, hl⟩).val.comap (Ideal.Quotient.mk I),
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
