/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/

import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Order.Monoid.Submonoid -- TODO : downstream
import Mathlib.Algebra.Order.Group.Unbundled.Basic -- TODO : downstream

/-!
# Supports of submonoids

Let `G` be an (additive) group, and let `M` be a submonoid of `G`.
The *support* of `M` is `M ∩ -M`, the largest subgroup of `M`.
A (strict, additive group) *cone* is a submonoid `C` with zero support.
A cone `C` is *generating* if `C - C = M`.

We define these concepts for submonoids, but they are also relevant to subsemirings
and to convex cones. Strict cones correspond to ordered structures; see `Mathlib.Order.Cone`.

## Main definitions

* `AddSubmonoid.support`: the support of a submonoid.
* `AddSubmonoid.IsStrictCone`: typeclass for cones.
* `AddSubmonoid.IsGeneratingCone`: typeclass for submonoids `M` satisfying `M - M = G`.

-/

-- TODO : Convex Cone version

namespace AddSubmonoid

variable {G : Type*} [AddGroup G] (M : AddSubmonoid G)

/-- Typeclass for submonoids with zero mulSupport. -/
class IsStrictCone (M : AddSubmonoid G) : Prop where
  eq_zero_of_mem_of_neg_mem {x} (hx₁ : x ∈ M) (hx₂ : -x ∈ M) : x = 0 := by aesop

export IsStrictCone (eq_zero_of_mem_of_neg_mem)

attribute [aesop 50% apply, aesop safe forward (immediate := [hx₁])] eq_zero_of_mem_of_neg_mem

/-- Typeclass for submonoids `M` of a group `G` such that `M - M = G`. -/
class IsGeneratingCone (M : AddSubmonoid G) : Prop where
  mem_or_neg_mem (M) (a : G) : a ∈ M ∨ -a ∈ M := by aesop

export IsGeneratingCone (mem_or_neg_mem)

attribute [aesop safe forward, aesop safe apply] mem_or_neg_mem

end AddSubmonoid

namespace Submonoid

variable {G : Type*} [Group G] (M : Submonoid G)

/--
The support of a submonoid `M` of a group `G` is `M ∩ M⁻¹`,
the largest subgroup contained in `M`.
-/
@[to_additive
/-- The support of a submonoid `M` of a group `G` is `M ∩ -M`,
the largest subgroup contained in `M`. -/]
def mulSupport : Subgroup G where
  carrier := M ∩ M⁻¹
  one_mem' := by aesop
  mul_mem' := by aesop
  inv_mem' := by aesop

variable {M} in
@[to_additive (attr := aesop simp)]
theorem mem_mulSupport {x} : x ∈ M.mulSupport ↔ x ∈ M ∧ x⁻¹ ∈ M := .rfl

@[to_additive]
theorem coe_mulSupport : M.mulSupport = (M ∩ M⁻¹ : Set G) := rfl

variable {G : Type*} [Group G] (M : Submonoid G)

/-- Typeclass for submonoids with zero support. -/
@[to_additive IsStrictCone]
class IsStrictMulCone (M : Submonoid G) : Prop where
  eq_one_of_mem_of_inv_mem {x} (hx₁ : x ∈ M) (hx₂ : x⁻¹ ∈ M) : x = 1 := by aesop

export IsStrictMulCone (eq_one_of_mem_of_inv_mem)

attribute [aesop 50% apply, aesop safe forward (immediate := [hx₁])] eq_one_of_mem_of_inv_mem

@[to_additive (attr := aesop safe forward (immediate := [hx₂]))]
alias eq_one_of_mem_of_inv_mem₂ := eq_one_of_mem_of_inv_mem -- for Aesop

@[to_additive (attr := simp)]
theorem mulSupport_eq_bot [M.IsStrictMulCone] : M.mulSupport = ⊥ := by ext; aesop

@[to_additive]
theorem IsStrictMulCone.of_support_eq_bot (h : M.mulSupport = ⊥) : M.IsStrictMulCone where
  eq_one_of_mem_of_inv_mem {x} := by
    apply_fun (x ∈ ·) at h
    aesop

/-- Typeclass for submonoids `M` of a group `G` such that `M * M⁻¹ = G`. -/
@[to_additive IsGeneratingCone]
class IsGeneratingMulCone {G : Type*} [Group G] (M : Submonoid G) : Prop where
  mem_or_inv_mem (M) (a : G) : a ∈ M ∨ a⁻¹ ∈ M := by aesop

export IsGeneratingMulCone (mem_or_inv_mem)

attribute [aesop safe forward, aesop safe apply] mem_or_inv_mem

@[to_additive]
theorem IsGeneratingMulCone.of_le {M N : Submonoid G} [M.IsGeneratingMulCone] (h : M ≤ N) :
    N.IsGeneratingMulCone where
  mem_or_inv_mem a := by aesop

@[to_additive]
theorem IsGeneratingMulCone.maximal [M.IsStrictMulCone] [M.IsGeneratingMulCone] :
    Maximal IsStrictMulCone M :=
  ⟨inferInstance, fun N hN h ↦ by rw [SetLike.le_def] at h ⊢; aesop⟩

end Submonoid

-- PR SPLIT ↑1 ↓2

namespace Submonoid

section Group

variable {G H : Type*} [Group G] [Group H] (f : G →* H) (M N : Submonoid G) (M' : Submonoid H)
         {s : Set (Submonoid G)}

variable {M N} in
@[to_additive]
theorem mulSupport_mono (h : M ≤ N) : M.mulSupport ≤ N.mulSupport := fun _ ↦ by aesop -- TODO : aesop intro on inequalities

@[to_additive (attr := simp)]
theorem mulSupport_inf : (M ⊓ N).mulSupport = M.mulSupport ⊓ N.mulSupport := by aesop

@[to_additive (attr := simp)]
theorem mulSupport_sInf (s : Set (Submonoid G)) :
    (sInf s).mulSupport = InfSet.sInf (mulSupport '' s) := by aesop

@[to_additive (attr := simp)]
theorem mulSupport_sSup (hsn : s.Nonempty) (hsd : DirectedOn (· ≤ ·) s) :
    (sSup s).mulSupport = SupSet.sSup (mulSupport '' s) := by
  ext x
  rw [Subgroup.mem_sSup_of_directedOn (by simp_all)
       (.mono_comp (fun _ _ h ↦ mulSupport_mono h) hsd)]
  simp only [mem_mulSupport, mem_sSup_of_directedOn, Set.mem_image,
    exists_exists_and_eq_and, hsd, hsn]
  refine ⟨?_, by aesop⟩
  rintro ⟨⟨_, hx₁, _⟩, ⟨_, hx₂, _⟩⟩
  rcases hsd _ hx₁ _ hx₂ with ⟨x, _⟩
  exact ⟨x, by aesop⟩

@[to_additive]
instance [M'.IsGeneratingMulCone] : (M'.comap f).IsGeneratingMulCone where
  mem_or_inv_mem x := by aesop

@[to_additive (attr := simp)]
theorem comap_mulSupport : (M'.comap f).mulSupport = (M'.mulSupport).comap f := by aesop

variable {f} in
@[to_additive]
theorem IsGeneratingCone.map [M.IsGeneratingMulCone] (hf : Function.Surjective f) :
    (M.map f).IsGeneratingMulCone where
  mem_or_inv_mem x := by
    obtain ⟨x', rfl⟩ := hf x
    aesop

end Group

section CommGroup

variable {G H : Type*} [CommGroup G] [CommGroup H] (f : G →* H) (M : Submonoid G)

variable {f M} in
@[to_additive (attr := simp)]
theorem map_mulSupport
    (hsupp : f.ker ≤ M.mulSupport) :
    (M.map f).mulSupport = (M.mulSupport).map f := by
  ext
  refine ⟨fun ⟨⟨a, ⟨ha₁, ha₂⟩⟩, ⟨b, ⟨hb₁, hb₂⟩⟩⟩ => ?_, by aesop⟩
  have : (a * b)⁻¹ * b ∈ M := by exact mul_mem (hsupp (show f (a * b) = 1 by simp_all)).2 hb₁
  aesop

end CommGroup

section downstream

variable (G : Type*) [CommGroup G]

-- TODO : downstream to `Mathlib.Algebra.Order.Monoid.Submonoid` or further

@[to_additive]
instance [PartialOrder G] [IsOrderedMonoid G] : (oneLE G).IsStrictMulCone where
  eq_one_of_mem_of_inv_mem := by simp_all [ge_antisymm_iff]

@[to_additive]
instance [LinearOrder G] [IsOrderedMonoid G] : (oneLE G).IsGeneratingMulCone where
  mem_or_inv_mem := by simpa using le_total (1 : G)

end downstream

end Submonoid
