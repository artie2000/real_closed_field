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
A submonoid `C` is *pointed*, or a *positive cone*, if it has zero support.
A submonoid `C` is *spanning* if the subgroup it generates is `G` itself.

The names for these concepts are taken from the theory of convex cones.

## Main definitions

* `AddSubmonoid.support`: the support of a submonoid.
* `AddSubmonoid.IsPointed`: typeclass for submonoids with zero support.
* `AddSubmonoid.IsSpanning`: typeclass for submonoids generating the whole group.

-/

-- TODO : add to_additive cleanups AddPointed -> Pointed, AddSpanning -> Spanning

namespace AddSubmonoid

variable {G : Type*} [AddGroup G] (M : AddSubmonoid G)

/-- Typeclass for submonoids of a group with zero support. -/
class IsPointed (M : AddSubmonoid G) : Prop where
  eq_zero_of_mem_of_neg_mem {x} (hx₁ : x ∈ M) (hx₂ : -x ∈ M) : x = 0 := by aesop

export IsPointed (eq_zero_of_mem_of_neg_mem)

attribute [aesop 50% apply, aesop safe forward (immediate := [hx₁])] eq_zero_of_mem_of_neg_mem

/-- Typeclass for submonoids `M` of a group `G` such that `M` generates `G` as a subgroup. -/
class IsSpanning (M : AddSubmonoid G) : Prop where
  mem_or_neg_mem (M) (a : G) : a ∈ M ∨ -a ∈ M := by aesop

export IsSpanning (mem_or_neg_mem)

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

/-- Typeclass for submonoids of a group with zero support. -/
@[to_additive IsPointed]
class IsMulPointed (M : Submonoid G) : Prop where
  eq_one_of_mem_of_inv_mem {x} (hx₁ : x ∈ M) (hx₂ : x⁻¹ ∈ M) : x = 1 := by aesop

export IsMulPointed (eq_one_of_mem_of_inv_mem)

attribute [aesop 50% apply, aesop safe forward (immediate := [hx₁])] eq_one_of_mem_of_inv_mem

@[to_additive (attr := aesop safe forward (immediate := [hx₂]))]
alias eq_one_of_mem_of_inv_mem₂ := eq_one_of_mem_of_inv_mem -- for Aesop

@[to_additive (attr := simp)]
theorem mulSupport_eq_bot [M.IsMulPointed] : M.mulSupport = ⊥ := by ext; aesop

@[to_additive]
theorem IsMulPointed.of_mulSupport_eq_bot (h : M.mulSupport = ⊥) : M.IsMulPointed where
  eq_one_of_mem_of_inv_mem {x} := by
    apply_fun (x ∈ ·) at h
    aesop

/-- Typeclass for submonoids `M` of a group `G` such that `M` generates `G` as a subgroup. -/
@[to_additive IsSpanning]
class IsMulSpanning {G : Type*} [Group G] (M : Submonoid G) : Prop where
  mem_or_inv_mem (M) (a : G) : a ∈ M ∨ a⁻¹ ∈ M := by aesop

export IsMulSpanning (mem_or_inv_mem)

attribute [aesop safe forward, aesop safe apply] mem_or_inv_mem

@[to_additive]
theorem IsMulSpanning.of_le {M N : Submonoid G} [M.IsMulSpanning] (h : M ≤ N) :
    N.IsMulSpanning where

@[to_additive IsSpanning.maximal_isPointed]
theorem IsMulSpanning.maximal_isMulPointed [M.IsMulPointed] [M.IsMulSpanning] :
    Maximal IsMulPointed M :=
  ⟨inferInstance, fun N hN h ↦ by rw [SetLike.le_def] at h ⊢; aesop⟩

-- PR SPLIT ↑1 ↓2

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

@[to_additive]
instance [M'.IsMulSpanning] : (M'.comap f).IsMulSpanning where

@[to_additive (attr := simp)]
theorem comap_mulSupport : (M'.comap f).mulSupport = (M'.mulSupport).comap f := by aesop

variable {f} in
@[to_additive]
theorem IsMulSpanning.map [M.IsMulSpanning] (hf : Function.Surjective f) :
    (M.map f).IsMulSpanning where
  mem_or_inv_mem x := by
    obtain ⟨x', rfl⟩ := hf x
    aesop

end Group

section CommGroup

variable {G H : Type*} [CommGroup G] [CommGroup H] (f : G →* H) (M : Submonoid G)

variable {f M} in
@[to_additive (attr := simp)]
theorem map_mulSupport (hsupp : f.ker ≤ M.mulSupport) :
    (M.map f).mulSupport = (M.mulSupport).map f := by
  ext
  refine ⟨fun ⟨⟨a, ⟨ha₁, ha₂⟩⟩, ⟨b, ⟨hb₁, hb₂⟩⟩⟩ => ?_, by aesop⟩
  have : (a * b)⁻¹ * b ∈ M := by exact mul_mem (hsupp (show f (a * b) = 1 by simp_all)).2 hb₁
  aesop

end CommGroup

end Submonoid

section downstream

variable (G : Type*) [CommGroup G]

-- TODO : downstream to `Mathlib.Algebra.Order.Monoid.Submonoid` or further

@[to_additive]
instance [PartialOrder G] [IsOrderedMonoid G] : (Submonoid.oneLE G).IsMulPointed where
  eq_one_of_mem_of_inv_mem := by simp_all [ge_antisymm_iff]

@[to_additive]
instance [LinearOrder G] [IsOrderedMonoid G] : (Submonoid.oneLE G).IsMulSpanning where
  mem_or_inv_mem := by simpa using le_total (1 : G)

variable {G} (M : Submonoid G) [M.IsMulPointed]

/-- Construct a partial order by designating a submonoid with zero support in an abelian group. -/
@[to_additive
/-- Construct a partial order by designating a submonoid with zero support in an abelian group. -/]
abbrev PartialOrder.mkOfSubmonoid : PartialOrder G where
  le a b := b / a ∈ M
  le_refl a := by simp [one_mem]
  le_trans a b c nab nbc := by simpa using mul_mem nbc nab
  le_antisymm a b nab nba := by
    simpa [div_eq_one, eq_comm] using M.eq_one_of_mem_of_inv_mem nab (by simpa using nba)

variable {M} in
@[to_additive (attr := simp)]
theorem PartialOrder.mkOfSubmonoid_le_iff {a b : G} :
    (mkOfSubmonoid M).le a b ↔ b / a ∈ M := .rfl

@[to_additive]
theorem IsOrderedMonoid.mkOfSubmonoid :
    letI _ := PartialOrder.mkOfSubmonoid M
    IsOrderedMonoid G :=
  letI _ := PartialOrder.mkOfSubmonoid M
  { mul_le_mul_left := fun a b nab c ↦ by simpa [· ≤ ·] using nab }

/-- Construct a linear order by designating
    a maximal submonoid with zero support in an abelian group. -/
@[to_additive
/-- Construct a linear order by designating
    a maximal submonoid with zero support in an abelian group. -/]
abbrev LinearOrder.mkOfSubmonoid [M.IsMulSpanning] [DecidablePred (· ∈ M)] : LinearOrder G where
  __ := PartialOrder.mkOfSubmonoid M
  le_total a b := by simpa using M.mem_or_inv_mem (b / a)
  toDecidableLE _ := _

namespace CommGroup

variable (G) in
/-- Equivalence between submonoids with zero support in an abelian group `G`
    and partially ordered group structures on `G`. -/
@[to_additive
  /-- Equivalence between submonoids with zero support in an abelian group `G`
    and partially ordered group structures on `G`. -/]
noncomputable def submonoidPartialOrderEquiv :
    Equiv {C : Submonoid G // C.IsMulPointed}
          {o : PartialOrder G // IsOrderedMonoid G} where
  toFun := fun ⟨C, _⟩ => ⟨.mkOfSubmonoid C, .mkOfSubmonoid _⟩
  invFun := fun ⟨_, _⟩ => ⟨.oneLE G, inferInstance⟩
  left_inv := fun ⟨_, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by ext; simp

@[to_additive (attr := simp)]
theorem submonoidPartialOrderEquiv_apply
    (C : Submonoid G) (h : C.IsMulPointed) :
    submonoidPartialOrderEquiv G ⟨C, h⟩ = PartialOrder.mkOfSubmonoid C := rfl

@[to_additive (attr := simp)]
theorem submonoidPartialOrderEquiv_symm_apply (o : PartialOrder G) (h : IsOrderedMonoid G) :
    (submonoidPartialOrderEquiv G).symm ⟨o, h⟩ = Submonoid.oneLE G := rfl

open Classical in
variable (G) in
/-- Equivalence between maximal submonoids with zero support in an abelian group `G`
    and linearly ordered group structures on `G`. -/
@[to_additive
  /-- Equivalence between maximal submonoids with zero support in an abelian group `G`
    and linearly ordered group structures on `G`. -/]
noncomputable def submonoidLinearOrderEquiv :
    Equiv {C : Submonoid G // C.IsMulPointed ∧ C.IsMulSpanning}
          {o : LinearOrder G // IsOrderedMonoid G} where
  toFun := fun ⟨C, hC⟩ => have := hC.1; have := hC.2;
    ⟨.mkOfSubmonoid C, .mkOfSubmonoid C⟩
  invFun := fun ⟨_, _⟩ => ⟨.oneLE G, inferInstance, inferInstance⟩
  left_inv := fun ⟨_, _, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by ext; simp

open Classical in
@[to_additive (attr := simp)]
theorem submonoidLinearOrderEquiv_apply
    (C : Submonoid G) (h : C.IsMulPointed ∧ C.IsMulSpanning) :
    submonoidLinearOrderEquiv G ⟨C, h⟩ =
    have := h.1; have := h.2; LinearOrder.mkOfSubmonoid C := rfl

@[to_additive (attr := simp)]
theorem submonoidLinearOrderEquiv_symm_apply (l : LinearOrder G) (h : IsOrderedMonoid G) :
    (submonoidLinearOrderEquiv G).symm ⟨l, h⟩ = Submonoid.oneLE G := rfl

end CommGroup

end downstream
