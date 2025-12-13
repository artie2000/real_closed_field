-- TODO : fix copyright to acknowledge original author of cone files
/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.Algebra.Group.Submonoid.Support
import Mathlib.Algebra.Order.Monoid.Submonoid
import Mathlib.Algebra.Ring.Subsemiring.Order

/-!
# Positive cones

A *positive cone* in an (additive) group `G` is a submonoid `C` with zero support
(i.e. `C ∩ -C = 0`).

A *positive cone* in a ring `R` is a subsemiring `C` with zero (additive) support.
We re-use the predicate from the group case.

Positive cones in an abelian group `G` correspond to ordered group structures on `G`.
Positive cones in a ring `R` correspond to ordered ring structures on `R`.
In each case, the cone corresponds to the set of non-negative elements.
If the cone `C` satisfies `C ∪ -C = G`, the induced order is total.

## Main definitions

* `AddSubmonoid.IsCone`: typeclass for positive cones.
* `AddCommGroup.isConePartialOrderEquiv` and `AddCommGroup.isConeLinearOrderEquiv`: equivalence
between (maximal) cones in an abelian group `G` and (linearly) ordered group structures on `G`.
* `Ring.isConePartialOrderEquiv` and `Ring.isConeLinearOrderEquiv`: equivalence
between (maximal) cones in an ring `R` and (linearly) ordered ring structures on `R`.

-/

-- TODO : register `to_additive` naming rule `IsMulCone` -> `IsCone` and remove explicit name annotations

-- TODO : upstream
@[simp]
theorem Subsemiring.nonneg_toAddSubmonoid
    (R : Type*) [Semiring R] [PartialOrder R] [IsOrderedRing R] :
  (nonneg R).toAddSubmonoid = AddSubmonoid.nonneg R := by ext; simp

namespace AddSubmonoid

variable {G : Type*} [AddGroup G] (M : AddSubmonoid G)

/-- Typeclass for submonoids with zero support. -/
class IsCone (M : AddSubmonoid G) : Prop where
  supportAddSubgroup_eq_bot (M) : M.supportAddSubgroup = ⊥

export IsCone (supportAddSubgroup_eq_bot)

attribute [simp] supportAddSubgroup_eq_bot

end AddSubmonoid

namespace Submonoid

section Group

variable {G : Type*} [Group G] (M : Submonoid G)

/-- Typeclass for submonoids with zero support. -/
@[to_additive IsCone]
class IsMulCone (M : Submonoid G) : Prop where
  supportSubgroup_eq_bot (M) : M.supportSubgroup = ⊥

export IsMulCone (supportSubgroup_eq_bot)

variable {M} in
@[to_additive isCone_iff]
theorem isMulCone_iff : M.IsMulCone ↔ ∀ x : G, x ∈ M → x⁻¹ ∈ M → x = 1 where
  mp _ x := by
    have := IsMulCone.supportSubgroup_eq_bot M
    apply_fun (x ∈ ·) at this
    aesop (add simp mem_supportSubgroup)
  mpr _ := ⟨by ext; aesop (add simp mem_supportSubgroup)⟩

variable {M} in
@[to_additive]
theorem eq_one_of_mem_of_inv_mem [M.IsMulCone]
    {x : G} (hx₁ : x ∈ M) (hx₂ : x⁻¹ ∈ M) : x = 1 :=
  isMulCone_iff.mp (inferInstance : M.IsMulCone) x hx₁ hx₂

attribute [simp] supportSubgroup_eq_bot

end Group

section CommGroup

variable (G : Type*) [CommGroup G]

@[to_additive]
instance [PartialOrder G] [IsOrderedMonoid G] : (oneLE G).IsMulCone where
  supportSubgroup_eq_bot := by
    ext
    simp [mem_supportSubgroup, ge_antisymm_iff]

@[to_additive]
instance [LinearOrder G] [IsOrderedMonoid G] : (oneLE G).HasMemOrInvMem where
  mem_or_inv_mem := by simpa using le_total 1

end CommGroup

end Submonoid

namespace AddSubmonoid

variable {R : Type*} [Ring R] (M : AddSubmonoid R)

instance [M.IsCone] : M.HasIdealSupport where
  smul_mem_support := by simp [supportAddSubgroup_eq_bot]

@[simp]
theorem support_eq_bot [M.IsCone] : M.support = ⊥ := by
  apply_fun Submodule.toAddSubgroup using Submodule.toAddSubgroup_injective
  exact supportAddSubgroup_eq_bot M

theorem IsCone.of_support_eq_bot [M.HasIdealSupport] (h : M.support = ⊥) : M.IsCone where
  supportAddSubgroup_eq_bot := by simp [h]

theorem IsCone.maximal [M.IsCone] [M.HasMemOrNegMem] : Maximal IsCone M :=
  ⟨inferInstance, fun N hN h ↦ by
    by_contra h2
    have ⟨x, hx, hx2⟩ : ∃ x, x ∈ N ∧ x ∉ M := Set.not_subset.mp h2
    have : -x ∈ N := by aesop (add unsafe forward (M.mem_or_neg_mem))
    have := AddSubmonoid.eq_zero_of_mem_of_neg_mem (M := N) (x := x)
    simp_all⟩

end AddSubmonoid

-- TODO : check if these instances can be removed once definition of `Subsemiring.nonneg` changes
namespace Subsemiring

variable (R : Type*) [Ring R]

instance [LinearOrder R] [IsOrderedRing R] : (nonneg R).HasMemOrNegMem := by
  simpa using (inferInstance : (AddSubmonoid.nonneg R).HasMemOrNegMem)

instance [PartialOrder R] [IsOrderedRing R] : (nonneg R).IsCone := by
  simpa using (inferInstance : (AddSubmonoid.nonneg R).IsCone)

end Subsemiring

section CommGroup

variable {G : Type*} [CommGroup G] (S : Submonoid G) [S.IsMulCone]

/-- Construct a partial order by designating a cone in an abelian group. -/
@[to_additive /-- Construct a partial order by designating a cone in an abelian group. -/]
abbrev PartialOrder.mkOfSubmonoid : PartialOrder G where
  le a b := b / a ∈ S
  le_refl a := by simp [one_mem]
  le_trans a b c nab nbc := by simpa using mul_mem nbc nab
  le_antisymm a b nab nba := by
    simpa [div_eq_one, eq_comm] using Submonoid.eq_one_of_mem_of_inv_mem nab (by simpa using nba)

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
  le_total a b := by simpa using Submonoid.HasMemOrInvMem.mem_or_inv_mem S (b / a)
  toDecidableLE _ := _

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
