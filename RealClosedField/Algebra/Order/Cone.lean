/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Artie Khovanov
-/
import RealClosedField.Algebra.Order.Cone.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Equivalence between positive cones and order structures

Positive cones in an abelian group `G` correspond to ordered group structures on `G`.
Positive cones in a ring `R` correspond to ordered ring structures on `R`.
In each case, the cone corresponds to the set of non-negative elements.
If the cone `C` satisfies `C ∪ -C = ⊤`, the induced order is total.

## Main definitions

* `AddCommGroup.isConePartialOrderEquiv` and `AddCommGroup.isConeLinearOrderEquiv`: equivalence
between (maximal) cones in an abelian group `G` and (linearly) ordered group structures on `G`.
* `Ring.isConePartialOrderEquiv` and `Ring.isConeLinearOrderEquiv`: equivalence
between (maximal) cones in an ring `R` and (linearly) ordered ring structures on `R`.
* `AddCommGroup.addSubmonoidPartialOrderEquiv` and `AddCommGroup.addSubmonoidLinearOrderEquiv`:
equivalence between submonoids `H` of an abelian group `G` (satisfying `H ∪ -H = G`) and
(linearly) ordered group structures on `R ⧸ H.supportAddSubgroup`.
* `Ring.subsemiringPartialOrderEquiv` and `Ring.subsemiringPartialOrderEquiv`: equivalence
between subsemirings `S` of a ring `R` (satisfying `S ∪ -S = R`) and
(linearly) ordered ring structures on `R ⧸ S.support`.

-/

section CommGroup

variable {G : Type*} [CommGroup G] (S : Submonoid G) [S.IsMulCone]

/-- Construct a partial order by designating a cone in an abelian group. -/
@[to_additive /-- Construct a partial order by designating a cone in an abelian group. -/]
abbrev PartialOrder.mkOfSubmonoid : PartialOrder G where
  le a b := b / a ∈ S
  le_refl a := by simp [one_mem]
  le_trans a b c nab nbc := by simpa using mul_mem nbc nab
  le_antisymm a b nab nba := by
    simpa [div_eq_one, eq_comm] using S.eq_one_of_mem_of_inv_mem nab (by simpa using nba)

variable {S} in
@[to_additive (attr := simp)]
theorem PartialOrder.mkOfSubmonoid_le_iff {a b : G} :
    (mkOfSubmonoid S).le a b ↔ b / a ∈ S := Iff.rfl

/-- Construct an ordered abelian group by designating a cone in an abelian group. -/
@[to_additive
  /-- Construct an ordered abelian group by designating a cone in an abelian group. -/]
theorem IsOrderedMonoid.mkOfSubmonoid :
    letI _ := PartialOrder.mkOfSubmonoid S
    IsOrderedMonoid G :=
  letI _ := PartialOrder.mkOfSubmonoid S
  { mul_le_mul_left := fun a b nab c ↦ by simpa [· ≤ ·] using nab }

/-- Construct a linear order by designating a maximal cone in an abelian group. -/
@[to_additive /-- Construct a linear order by designating a maximal cone in an abelian group. -/]
abbrev LinearOrder.mkOfSubmonoid [S.HasMemOrInvMem] [DecidablePred (· ∈ S)] : LinearOrder G where
  __ := PartialOrder.mkOfSubmonoid S
  le_total a b := by simpa using S.mem_or_inv_mem (b / a)
  toDecidableLE _ := _

-- PR SPLIT ↑1 ↓2

namespace CommGroup

variable (G) in
/-- Equivalence between cones in an abelian group `G`
    and partially ordered group structures on `G`. -/
@[to_additive isConePartialOrderEquiv
  /-- Equivalence between cones in an abelian group `G`
    and partially ordered group structures on `G`. -/]
noncomputable def isMulConePartialOrderEquiv :
    Equiv {C : Submonoid G // C.IsMulCone}
          {o : PartialOrder G // IsOrderedMonoid G} where
  toFun := fun ⟨C, _⟩ => ⟨.mkOfSubmonoid C, .mkOfSubmonoid _⟩
  invFun := fun ⟨_, _⟩ => ⟨.oneLE G, inferInstance⟩
  left_inv := fun ⟨_, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by ext; simp

@[to_additive (attr := simp) isConePartialOrderEquiv_apply]
theorem isMulConePartialOrderEquiv_apply
    (C : Submonoid G) (h : C.IsMulCone) :
    isMulConePartialOrderEquiv G ⟨C, h⟩ = PartialOrder.mkOfSubmonoid C := rfl

@[to_additive (attr := simp) isConePartialOrderEquiv_symm_apply]
theorem isMulConePartialOrderEquiv_symm_apply (o : PartialOrder G) (h : IsOrderedMonoid G) :
    (isMulConePartialOrderEquiv G).symm ⟨o, h⟩ = Submonoid.oneLE G := rfl

open Classical in
variable (G) in
/-- Equivalence between maximal cones in an abelian group `G`
    and linearly ordered group structures on `G`. -/
@[to_additive isConeLinearOrderEquiv
  /-- Equivalence between maximal cones in an abelian group `G`
    and linearly ordered group structures on `G`. -/]
noncomputable def isMulConeLinearOrderEquiv :
    Equiv {C : Submonoid G // C.IsMulCone ∧ C.HasMemOrInvMem}
          {o : LinearOrder G // IsOrderedMonoid G} where
  toFun := fun ⟨C, hC⟩ => have := hC.1; have := hC.2;
    ⟨.mkOfSubmonoid C, .mkOfSubmonoid C⟩
  invFun := fun ⟨_, _⟩ => ⟨.oneLE G, inferInstance, inferInstance⟩
  left_inv := fun ⟨_, _, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by ext; simp

open Classical in
@[to_additive (attr := simp) isConeLinearOrderEquiv_apply]
theorem isMulConeLinearOrderEquiv_apply
    (C : Submonoid G) (h : C.IsMulCone ∧ C.HasMemOrInvMem) :
    isMulConeLinearOrderEquiv G ⟨C, h⟩ =
    have := h.1; have := h.2; LinearOrder.mkOfSubmonoid C := rfl

@[to_additive (attr := simp) isConeLinearOrderEquiv_symm_apply]
theorem isMulConeLinearOrderEquiv_symm_apply (l : LinearOrder G) (h : IsOrderedMonoid G) :
    (isMulConeLinearOrderEquiv G).symm ⟨l, h⟩ = Submonoid.oneLE G := rfl

end CommGroup

-- PR SPLIT ↑2 ↓1

section Ring

variable {R : Type*} [Ring R]

/-- Construct an ordered ring by designating a cone in a ring. -/
theorem IsOrderedRing.mkOfSubsemiring (S : Subsemiring R) [S.IsCone] :
    letI _ := PartialOrder.mkOfAddSubmonoid S.toAddSubmonoid
    IsOrderedRing R :=
  letI _ := PartialOrder.mkOfAddSubmonoid S.toAddSubmonoid
  haveI := IsOrderedAddMonoid.mkOfAddSubmonoid S.toAddSubmonoid
  haveI : ZeroLEOneClass R := ⟨by simp⟩
  .of_mul_nonneg fun x y xnn ynn ↦ show _ ∈ S by simpa using Subsemiring.mul_mem _ xnn ynn

-- PR SPLIT ↑1 ↓2

namespace Ring

variable (R) in
/-- Equivalence between cones in a ring `R` and partially ordered ring structures on `R`. -/
noncomputable def isConePartialOrderEquiv :
    Equiv {C : Subsemiring R // C.IsCone}
          {o : PartialOrder R // IsOrderedRing R} where
  toFun := fun ⟨C, _⟩ => ⟨.mkOfAddSubmonoid C.toAddSubmonoid, .mkOfSubsemiring _⟩
  invFun := fun ⟨_, _⟩ => ⟨.nonneg R, inferInstance⟩
  left_inv := fun ⟨_, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by ext; simp

@[simp]
theorem isConePartialOrderEquiv_apply
    (C : Subsemiring R) (h : C.IsCone) :
    isConePartialOrderEquiv R ⟨C, h⟩ = PartialOrder.mkOfAddSubmonoid C.toAddSubmonoid := rfl

@[simp]
theorem isConePartialOrderEquiv_symm_apply (o : PartialOrder R) (h : IsOrderedRing R) :
    (isConePartialOrderEquiv R).symm ⟨o, h⟩ = Subsemiring.nonneg R := rfl

variable (R) in
open Classical in
/-- Equivalence between maximal cones in a ring `R` and linearly ordered ring structures on `R`. -/
noncomputable def isConeLinearOrderEquiv :
    Equiv {C : Subsemiring R // C.IsCone ∧ C.HasMemOrNegMem}
          {o : LinearOrder R // IsOrderedRing R} where
  toFun := fun ⟨C, hC⟩ => have := hC.1; have := hC.2;
    ⟨.mkOfAddSubmonoid C.toAddSubmonoid, .mkOfSubsemiring C⟩
  invFun := fun ⟨_, _⟩ => ⟨.nonneg R, by simp; infer_instance, by simp; infer_instance⟩
  left_inv := fun ⟨_, _, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by ext; simp

open Classical in
@[simp]
theorem isConeLinearOrderEquiv_apply
    (C : Subsemiring R) (h : C.IsCone ∧ C.HasMemOrNegMem) :
    isConeLinearOrderEquiv R ⟨C, h⟩ =
    have := h.1; have := h.2; LinearOrder.mkOfAddSubmonoid C.toAddSubmonoid := rfl

@[simp]
theorem isConeLinearOrderEquiv_symm_apply (o : LinearOrder R) (h : IsOrderedRing R) :
    (isConeLinearOrderEquiv R).symm ⟨o, h⟩ = Subsemiring.nonneg R := rfl

end Ring

end Ring

-- PR SPLIT ↑2 ↓3

/- TODO : quotient versions: need to lift the constructions to prop equality?

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

-- end upstream

section Quot

-- TODO : group and partial versions

variable {R : Type*} [CommRing R] (O : Subsemiring R) [O.HasMemOrNegMem]

instance : (O.map (Ideal.Quotient.mk O.support)).HasMemOrNegMem :=
  AddSubmonoid.HasMemOrNegMem.map O.toAddSubmonoid
    (f := (Ideal.Quotient.mk O.support).toAddMonoidHom) Ideal.Quotient.mk_surjective

-- TODO : move to right place
@[simp]
theorem RingHom.ker_toAddSubgroup {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
  (RingHom.ker f).toAddSubgroup = f.toAddMonoidHom.ker := by ext; simp

-- TODO : make proof less awful
instance : (O.map (Ideal.Quotient.mk O.support)).IsCone where
  supportAddSubgroup_eq_bot := by
    have : (O.toAddSubmonoid.map (Ideal.Quotient.mk O.support).toAddMonoidHom).HasIdealSupport := by
      simpa using (inferInstance : (O.map (Ideal.Quotient.mk O.support)).HasIdealSupport)
    have fact : (Ideal.Quotient.mk O.support).toAddMonoidHom.ker = O.supportAddSubgroup := by
      have := Ideal.mk_ker (I := O.support)
      apply_fun Submodule.toAddSubgroup at this
      simpa [-Ideal.mk_ker, -RingHom.toAddMonoidHom_eq_coe]
    have : (Ideal.Quotient.mk O.support).toAddMonoidHom.ker ≤ O.supportAddSubgroup := by
      simp [-RingHom.toAddMonoidHom_eq_coe, fact]
    have := AddSubmonoid.map_support Ideal.Quotient.mk_surjective this
    simp [-RingHom.toAddMonoidHom_eq_coe, this]

abbrev PartialOrder.mkOfSubsemiring_quot : PartialOrder (R ⧸ O.support) :=
  .mkOfAddSubmonoid (O.map (Ideal.Quotient.mk O.support)).toAddSubmonoid

theorem IsOrderedRing.mkOfSubsemiring_quot :
    letI  _ := PartialOrder.mkOfSubsemiring_quot O
    IsOrderedRing (R ⧸ O.support) := .mkOfSubsemiring (O.map (Ideal.Quotient.mk O.support))

abbrev LinearOrder.mkOfSubsemiring_quot [DecidablePred (· ∈ O)] : LinearOrder (R ⧸ O.support) :=
  have : DecidablePred (· ∈ O.map (Ideal.Quotient.mk O.support)) := by
    simpa using decidablePred_mem_map_quotient_mk (O.support)
      (by simp [AddSubmonoid.coe_support])
  .mkOfAddSubmonoid (O.map (Ideal.Quotient.mk O.support)).toAddSubmonoid

-- TODO : come up with correct statement and name
open Classical in
noncomputable def subsemiringLinearOrderEquiv (I : Ideal R) :
    Equiv {O : Subsemiring R // ∃ _ : O.HasMemOrNegMem, O.support = I}
          {o : LinearOrder (R ⧸ I) // IsOrderedRing (R ⧸ I)} where
  toFun := fun ⟨O, hO⟩ => have := hO.1; have hs := hO.2; ⟨by rw [← hs]; exact .mkOfSubsemiring_quot O, .mkOfSubsemiring_quot O⟩
  invFun := fun ⟨o, ho⟩ =>
    ⟨((Ring.isConeLinearOrderEquiv _).symm ⟨o, ho⟩).val.comap (Ideal.Quotient.mk I),
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

-/
