/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Artie Khovanov
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

Positive cones correspond to ordered group structures: see `Algebra.Order.Cone.Order`.

## Main definitions

* `AddSubmonoid.IsCone`: typeclass for positive cones.

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

namespace Subsemiring

variable {R : Type*} [Ring R] (C : Subsemiring R)

@[aesop simp (rule_sets := [SetLike])]
theorem IsCone.neg_one_notMem [Nontrivial R] [C.IsCone] : -1 ∉ C := fun hc ↦ by
  simpa [C.eq_zero_of_mem_of_neg_mem (by simp) hc] using zero_ne_one' R

-- TODO : check if these instances can be removed once definition of `Subsemiring.nonneg` changes
instance [LinearOrder R] [IsOrderedRing R] : (nonneg R).HasMemOrNegMem := by
  simpa using (inferInstance : (AddSubmonoid.nonneg R).HasMemOrNegMem)

instance [PartialOrder R] [IsOrderedRing R] : (nonneg R).IsCone := by
  simpa using (inferInstance : (AddSubmonoid.nonneg R).IsCone)

end Subsemiring
