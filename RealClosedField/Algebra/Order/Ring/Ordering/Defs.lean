/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Ring.SumsOfSquares

/-!
# Ring orderings

Let `R` be a commutative ring. A preordering on `R` is a subset closed under
addition and multiplication that contains all squares, but not `-1`.

The support of a preordering `P` is the set of elements `x` such that both `x` and `-x` lie in `P`.

An ordering `O` on `R` is a preordering such that
1. `O` contains either `x` or `-x` for each `x` in `R` and
2. the support of `O` is a prime ideal.

We define preorderings, supports and orderings.

An ordering can intuitively be viewed as a set of "non-negative" ring elements.
Indeed, an ordering `O` with support `p` induces a linear order on `R⧸p` making it
into an ordered ring, and vice versa.

## References

- [*An introduction to real algebra*, T.Y. Lam][lam_1984]

-/

-- TODO : update docstrings

namespace AddSubmonoid

variable {G : Type*} [AddGroup G] (S : AddSubmonoid G)

/-- Typeclass for substructures `S` such that `S ∪ -S = G`. -/
class HasMemOrNegMem {G : Type*} [AddGroup G] (S : AddSubmonoid G) : Prop where
  mem_or_neg_mem (S) (a : G) : a ∈ S ∨ -a ∈ S

export HasMemOrNegMem (mem_or_neg_mem)

/--
The support of a subsemiring `S` of a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `S`.
-/
def supportAddSubgroup : AddSubgroup G where
  carrier := S ∩ -S
  zero_mem' := by aesop
  add_mem' := by aesop
  neg_mem' := by aesop

class IsAddCone (S : AddSubmonoid G) : Prop where
  supportAddSubgroup_eq_bot (S) : S.supportAddSubgroup = ⊥

export IsAddCone (supportAddSubgroup_eq_bot)

attribute [simp] supportAddSubgroup_eq_bot

end AddSubmonoid

namespace Submonoid

variable {G : Type*} [Group G] (S : Submonoid G)

/-- Typeclass for substructures `S` such that `S ∪ S⁻¹ = G`. -/
@[to_additive]
class HasMemOrInvMem {G : Type*} [Group G] (s : Submonoid G) : Prop where
  mem_or_inv_mem (s) (a : G) : a ∈ s ∨ a⁻¹ ∈ s

export HasMemOrInvMem (mem_or_inv_mem)

@[to_additive]
theorem HasMemOrInvMem.of_le {s t : Submonoid G} [s.HasMemOrInvMem] (h : s ≤ t) :
    t.HasMemOrInvMem where
  mem_or_inv_mem a := by aesop (add unsafe forward (s.mem_or_inv_mem a))

/--
The support of a subsemiring `S` of a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `S`.
-/
@[to_additive existing]
def supportSubgroup : Subgroup G where
  carrier := S ∩ S⁻¹
  one_mem' := by aesop
  mul_mem' := by aesop
  inv_mem' := by aesop

variable {S} in
@[to_additive]
theorem mem_supportSubgroup {x} : x ∈ S.supportSubgroup ↔ x ∈ S ∧ x⁻¹ ∈ S := .rfl

@[to_additive]
theorem coe_supportSubgroup : S.supportSubgroup = (S ∩ S⁻¹ : Set G) := rfl

@[to_additive IsAddCone]
class IsCone (S : Submonoid G) : Prop where
  supportSubgroup_eq_bot (S) : S.supportSubgroup = ⊥

export IsCone (supportSubgroup_eq_bot)

variable {S} in
@[to_additive AddSubmonoid.isAddCone_iff]
theorem isCone_iff : S.IsCone ↔ ∀ x : G, x ∈ S → x⁻¹ ∈ S → x = 1 where
  mp _ x := by
    have := IsCone.supportSubgroup_eq_bot S
    apply_fun (x ∈ ·) at this
    aesop (add simp mem_supportSubgroup)
  mpr _ := ⟨by ext; aesop (add simp mem_supportSubgroup)⟩

variable {S} in
@[to_additive]
theorem eq_one_of_mem_of_inv_mem [S.IsCone]
    {x : G} (hx₁ : x ∈ S) (hx₂ : x⁻¹ ∈ S) : x = 1 :=
  isCone_iff.mp (inferInstance : S.IsCone) x hx₁ hx₂

attribute [simp] supportSubgroup_eq_bot

end Submonoid

section Ring

variable {R : Type*} [Ring R]

namespace AddSubmonoid

variable (S : AddSubmonoid R)

/-- Typeclass to track whether the support of a subsemiring forms an ideal. -/
class HasIdealSupport (S : AddSubmonoid R) : Prop where
  smul_mem_support (S) (x : R) {a : R} (ha : a ∈ S.supportAddSubgroup) :
    x * a ∈ S.supportAddSubgroup

export HasIdealSupport (smul_mem_support)

variable {S} in
theorem hasIdealSupport_iff :
    S.HasIdealSupport ↔ ∀ x a : R, a ∈ S → -a ∈ S → x * a ∈ S ∧ -(x * a) ∈ S where
  mp _ := by simpa [mem_supportAddSubgroup] using smul_mem_support S
  mpr _ := ⟨by simpa [mem_supportAddSubgroup]⟩

instance [S.IsAddCone] : S.HasIdealSupport where
  smul_mem_support := by simp [supportAddSubgroup_eq_bot]

section HasIdealSupport

variable [HasIdealSupport S]

/--
The support of a subsemiring `S` of a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `P`.
-/
def support : Ideal R where
  __ := supportAddSubgroup S
  smul_mem' := by simpa [mem_supportAddSubgroup] using smul_mem_support S

variable {S} in
theorem mem_support {x} : x ∈ S.support ↔ x ∈ S ∧ -x ∈ S := .rfl

theorem coe_support : S.support = (S : Set R) ∩ -(S : Set R) := rfl

@[simp]
theorem supportAddSubgroup_eq : S.supportAddSubgroup = S.support.toAddSubgroup := rfl

@[simp]
theorem support_eq_bot [S.IsAddCone] : S.support = ⊥ := by
  apply_fun Submodule.toAddSubgroup using Submodule.toAddSubgroup_injective
  exact supportAddSubgroup_eq_bot S

theorem IsAddCone.of_support_eq_bot (h : S.support = ⊥) : S.IsAddCone where
  supportAddSubgroup_eq_bot := by simp [h]

end HasIdealSupport

end AddSubmonoid

namespace Subsemiring

variable (S : Subsemiring R)

instance [S.HasMemOrNegMem] : S.HasIdealSupport where
  smul_mem_support x a ha :=
    match S.mem_or_neg_mem x with
    | .inl hx => ⟨by simpa using Subsemiring.mul_mem S hx ha.1,
                  by simpa using Subsemiring.mul_mem S hx ha.2⟩
    | .inr hx => ⟨by simpa using Subsemiring.mul_mem S hx ha.2,
                  by simpa using Subsemiring.mul_mem S hx ha.1⟩

/--
An ordering `O` on a ring `R` is a subsemiring of `R` such that
1. `O` contains either `x` or `-x` for each `x` in `R` and
2. the support of `O` is a prime ideal.
-/
class IsOrdering extends S.HasMemOrNegMem, S.support.IsPrime

instance [IsDomain R] [S.HasMemOrNegMem] [S.IsAddCone] : S.IsOrdering where
  __ : S.support.IsPrime := by simpa using Ideal.bot_prime

/-- A preordering on a ring `R` is a subsemiring of `R` containing all squares,
but not containing `-1`. -/
class IsPreordering (S : Subsemiring R) : Prop where
  mem_of_isSquare (S) {x} (hx : IsSquare x) : x ∈ S := by aesop
  neg_one_notMem (S) : -1 ∉ S := by aesop

export IsPreordering (mem_of_isSquare)
export IsPreordering (neg_one_notMem)

attribute [aesop simp (rule_sets := [SetLike])] neg_one_notMem

section IsPreordering

variable [IsPreordering S]

@[aesop unsafe 80% (rule_sets := [SetLike])]
protected theorem mem_of_isSumSq {x : R} (hx : IsSumSq x) : x ∈ S := by
  induction hx with
  | zero => simp
  | sq_add => aesop (add unsafe mem_of_isSquare)

theorem sumSq_le {R : Type*} [CommRing R] (S : Subsemiring R) [IsPreordering S] :
    Subsemiring.sumSq R ≤ S := fun _ ↦ by
  simpa using Subsemiring.mem_of_isSumSq S

@[simp]
protected theorem mul_self_mem (x : R) : x * x ∈ S := by aesop

@[simp]
protected theorem pow_two_mem (x : R) : x ^ 2 ∈ S := by aesop

end IsPreordering

variable {S} in
theorem IsPreordering.of_support_neq_top [S.HasMemOrNegMem] (h : S.support ≠ ⊤) :
    S.IsPreordering where
  mem_of_isSquare x := by
    rcases x with ⟨y, rfl⟩
    cases S.mem_or_neg_mem y with
    | inl h => aesop
    | inr h => simpa using (show -y * -y ∈ S by aesop (config := { enableSimp := false }))
  neg_one_notMem hc := by
    have : 1 ∈ S.support := by simp [AddSubmonoid.mem_support, hc]
    exact h (by simpa [Ideal.eq_top_iff_one])

instance [Nontrivial R] [S.HasMemOrNegMem] [S.IsAddCone] : S.IsPreordering :=
  .of_support_neq_top (by simp)

/- An ordering is a preordering. -/
instance [S.IsOrdering] : S.IsPreordering :=
  .of_support_neq_top (Ideal.IsPrime.ne_top inferInstance)

end Subsemiring

end Ring
