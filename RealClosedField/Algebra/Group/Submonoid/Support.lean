/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/

import Mathlib.Algebra.Group.Submonoid.Support
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Order.Monoid.Submonoid
import Mathlib.Algebra.Order.Group.Unbundled.Basic

namespace Submonoid

-- begin #37252

section Group

variable {G H : Type*} [Group G] [Group H] (f : G →* H) (M N : Submonoid G) (M' : Submonoid H)
         {s : Set (Submonoid G)}

@[to_additive (attr := simp)]
theorem mulSupport_bot : (⊥ : Submonoid G).mulSupport = ⊥ := by ext; simp

@[to_additive (attr := simp)]
theorem mulSupport_top : (⊤ : Submonoid G).mulSupport = ⊤ := by ext; simp

variable {M N} in
@[to_additive]
theorem mulSupport_mono (h : M ≤ N) : M.mulSupport ≤ N.mulSupport := fun _ ↦ by
  have := mem_of_le_of_mem h
  grind [mem_mulSupport]

@[to_additive (attr := simp)]
theorem mulSupport_inf : (M ⊓ N).mulSupport = M.mulSupport ⊓ N.mulSupport := by
  ext
  grind [mem_mulSupport, Subgroup.mem_inf]

@[to_additive (attr := simp)]
theorem mulSupport_sInf (s : Set (Submonoid G)) :
    (sInf s).mulSupport = InfSet.sInf (mulSupport '' s) := by ext; simp; grind

variable {M'} in
@[to_additive]
theorem IsMulSpanning.comap (hM' : M'.IsMulSpanning) : (M'.comap f).IsMulSpanning := by
  grind [IsMulSpanning, mem_comap]

@[to_additive (attr := simp)]
theorem comap_mulSupport : (M'.comap f).mulSupport = (M'.mulSupport).comap f := by ext; simp

variable {f M} in
@[to_additive]
theorem IsMulSpanning.map (hM : M.IsMulSpanning) (hf : Function.Surjective f) :
    (M.map f).IsMulSpanning := fun x ↦ by
  obtain ⟨x', rfl⟩ := hf x
  grind [IsMulSpanning, mem_map]

end Group

section CommGroup

variable {G H : Type*} [CommGroup G] [CommGroup H] (f : G →* H) (M : Submonoid G)

variable {f M} in
@[to_additive (attr := simp)]
theorem map_mulSupport (hsupp : f.ker ≤ M.mulSupport) :
    (M.map f).mulSupport = (M.mulSupport).map f := by
  ext
  refine ⟨fun ⟨⟨a, ⟨ha₁, ha₂⟩⟩, ⟨b, ⟨hb₁, hb₂⟩⟩⟩ => ?_,
    by grind [Subgroup.mem_map, mem_map, mem_mulSupport]⟩
  have : (a * b)⁻¹ * b ∈ M := mul_mem (hsupp (show f (a * b) = 1 by simp_all)).2 hb₁
  grind [mem_mulSupport, SetLike.mem_coe, mul_inv_rev, inv_mul_cancel_comm, Subgroup.mem_map]

end CommGroup

end Submonoid

-- end #37252

section downstream -- `Mathlib.Algebra.Order.Group.Cone`

-- begin #37298

variable (G : Type*) [CommGroup G]

@[to_additive]
theorem Submonoid.oneLE.isMulPointed [PartialOrder G] [IsOrderedMonoid G] :
    (oneLE G).IsMulPointed := by simp_all [IsMulPointed, ge_antisymm_iff]

@[to_additive]
theorem Submonoid.oneLE.isMulSpanning [LinearOrder G] [IsOrderedMonoid G] :
    (oneLE G).IsMulSpanning := by simp_all [IsMulSpanning, le_total]

variable {G} {M : Submonoid G} (hM : M.IsMulPointed)

/-- Construct a partial order by designating a submonoid with zero support in an abelian group. -/
@[to_additive
/-- Construct a partial order by designating a submonoid with zero support in an abelian group. -/]
abbrev PartialOrder.mkOfSubmonoid : PartialOrder G where
  le a b := b / a ∈ M
  le_refl a := by simp [one_mem]
  le_trans a b c nab nbc := by simpa using mul_mem nbc nab
  le_antisymm a b nab nba := by
    simpa [div_eq_one, eq_comm] using hM.eq_one_of_mem_of_inv_mem nab (by simpa using nba)

variable {hM} in
@[to_additive (attr := simp)]
theorem PartialOrder.mkOfSubmonoid_le_iff {a b : G} :
    (mkOfSubmonoid hM).le a b ↔ b / a ∈ M := .rfl

@[to_additive]
theorem IsOrderedMonoid.mkOfSubmonoid :
    letI _ := PartialOrder.mkOfSubmonoid hM
    IsOrderedMonoid G :=
  letI _ := PartialOrder.mkOfSubmonoid hM
  { mul_le_mul_left := fun a b nab c ↦ by simpa [· ≤ ·] using nab }

/-- Construct a linear order by designating
    a maximal submonoid with zero support in an abelian group. -/
@[to_additive
/-- Construct a linear order by designating
    a maximal submonoid with zero support in an abelian group. -/]
abbrev LinearOrder.mkOfSubmonoid (hMs : M.IsMulSpanning) [DecidablePred (· ∈ M)] :
    LinearOrder G where
  __ := PartialOrder.mkOfSubmonoid hM
  le_total a b := by simpa using hMs.mem_or_inv_mem (b / a)
  toDecidableLE _ := _

-- end #37298

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
  toFun := fun ⟨_, hC⟩ => ⟨.mkOfSubmonoid hC, .mkOfSubmonoid _⟩
  invFun := fun ⟨_, _⟩ => ⟨.oneLE G, Submonoid.oneLE.isMulPointed G⟩
  left_inv := fun ⟨_, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by ext; simp [LE.le] -- TODO : figure out why [LE.le] works!

@[to_additive (attr := simp)]
theorem submonoidPartialOrderEquiv_apply
    (C : Submonoid G) (h : C.IsMulPointed) :
    submonoidPartialOrderEquiv G ⟨C, h⟩ = PartialOrder.mkOfSubmonoid h := rfl

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
  toFun := fun ⟨C, hC⟩ => ⟨.mkOfSubmonoid hC.1 hC.2, .mkOfSubmonoid hC.1⟩
  invFun := fun ⟨_, _⟩ => ⟨.oneLE G, Submonoid.oneLE.isMulPointed G, Submonoid.oneLE.isMulSpanning G⟩
  left_inv := fun ⟨_, _, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by ext; simp

open Classical in
@[to_additive (attr := simp)]
theorem submonoidLinearOrderEquiv_apply
    (C : Submonoid G) (h : C.IsMulPointed ∧ C.IsMulSpanning) :
    submonoidLinearOrderEquiv G ⟨C, h⟩ = LinearOrder.mkOfSubmonoid h.1 h.2 := rfl

@[to_additive (attr := simp)]
theorem submonoidLinearOrderEquiv_symm_apply (l : LinearOrder G) (h : IsOrderedMonoid G) :
    (submonoidLinearOrderEquiv G).symm ⟨l, h⟩ = Submonoid.oneLE G := rfl

end CommGroup
