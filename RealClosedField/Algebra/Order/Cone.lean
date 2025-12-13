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

Let `G` be an (additive, abelian) group.

A *positive cone* in an (additive) group `G` is a submonoid `C` with zero support
(i.e. `C ∩ -C = 0`).

A *positive cone* in a ring `R` is a subsemiring `C` with zero (additive) support.
We re-use the predicate from the group case.

Positive cones in an abelian group `G` correspond to ordered group structures on `G`.
Positive cones in a commutative ring `R` correspond to ordered ring structures on `R`.
In each case, the cone corresponds to the set of non-negative elements.
If the cone `C` satisfies `C ∪ -C = G`, the induced order is total.

## Main definitions

* `AddSubmonoid.IsCone`: typeclass for positive cones.
-- TODO : document the rest

-/

namespace AddSubmonoid

variable {G : Type*} [AddGroup G] (M : AddSubmonoid G)

/-- Typeclass for submonoids with zero support. -/
class IsCone (M : AddSubmonoid G) : Prop where
  supportAddSubgroup_eq_bot (M) : M.supportAddSubgroup = ⊥

export IsCone (supportAddSubgroup_eq_bot)

attribute [simp] supportAddSubgroup_eq_bot

end AddSubmonoid

namespace Submonoid

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

end Submonoid

namespace AddSubmonoid

section Ring

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

end Ring

end AddSubmonoid

namespace Submonoid

variable (G : Type*) [CommGroup G]

@[to_additive]
instance [LinearOrder G] [IsOrderedMonoid G] : (oneLE G).HasMemOrInvMem where
  mem_or_inv_mem := by simpa using le_total 1

@[to_additive]
instance [PartialOrder G] [IsOrderedMonoid G] : (oneLE G).IsMulCone where
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

variable {G : Type*} [CommGroup G] (S : Submonoid G) [S.IsMulCone]

/-- Construct a partial order by designating a cone in an abelian group. -/
@[to_additive /-- Construct a partial order by designating a cone in an abelian group. -/]
abbrev PartialOrder.mkOfSubmonoid : PartialOrder G where
  le a b := b / a ∈ S
  le_refl a := by simp [one_mem]
  le_trans a b c nab nbc := by simpa using mul_mem nbc nab
  le_antisymm a b nab nba := by
    simpa [div_eq_one, eq_comm] using Submonoid.eq_one_of_mem_of_inv_mem nab (by simpa using nba)

@[to_additive (attr := simp)]
theorem PartialOrder.mkOfSubmonoid_le_iff {a b : G} :
    (mkOfSubmonoid S).le a b ↔ b / a ∈ S := Iff.rfl

/-- Construct a partially ordered abelian group by designating a cone in an abelian group. -/
@[to_additive
  /-- Construct a partially ordered abelian group by designating a cone in an abelian group. -/]
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

end Group

section Ring

variable {R : Type*} [Ring R] (S : Subsemiring R) [S.IsCone]

/-- Construct a partially ordered ring by designating a cone in a ring. -/
theorem IsOrderedRing.mkOfSubsemiring :
    letI _ := PartialOrder.mkOfAddSubmonoid S.toAddSubmonoid
    IsOrderedRing R :=
  letI _ := PartialOrder.mkOfAddSubmonoid S.toAddSubmonoid
  haveI := IsOrderedAddMonoid.mkOfAddSubmonoid S.toAddSubmonoid
  haveI : ZeroLEOneClass R := ⟨by simp⟩
  .of_mul_nonneg fun x y xnn ynn ↦ show _ ∈ S by simpa using Subsemiring.mul_mem _ xnn ynn

end Ring

-- TODO : bundled equivs for these correspondences as in `Ordering.Order`
