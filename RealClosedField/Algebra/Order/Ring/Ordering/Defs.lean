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

A ring preordering can intuitively be viewed as a set of "non-negative" ring elements.
Indeed, an ordering `O` with support `p` induces a linear order on `R⧸p` making it
into an ordered ring, and vice versa.

## References

- [*An introduction to real algebra*, T.Y. Lam][lam_1984]

-/

/-!
#### Preorderings
-/

variable {R : Type*} [CommRing R] (S : Subsemiring R)

namespace Subsemiring

/-!
#### Support
-/

section supportAddSubgroup

/--
The support of a subsemiring `S` of a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `S`.
-/
def supportAddSubgroup : AddSubgroup R where
  carrier := S ∩ -S
  zero_mem' := by aesop
  add_mem' := by aesop
  neg_mem' := by aesop

variable {S} in
theorem mem_supportAddSubgroup {x} : x ∈ S.supportAddSubgroup ↔ x ∈ S ∧ -x ∈ S := .rfl

theorem coe_supportAddSubgroup : S.supportAddSubgroup = (S ∩ -S : Set R) := rfl

end supportAddSubgroup

/-- Typeclass to track whether the support of a subsemiring forms an ideal. -/
class HasIdealSupport (S : Subsemiring R) : Prop where
  smul_mem_support (S) (x : R) {a : R} (ha : a ∈ S.supportAddSubgroup) :
    x * a ∈ S.supportAddSubgroup

export HasIdealSupport (smul_mem_support)

theorem hasIdealSupport_iff :
    S.HasIdealSupport ↔ ∀ x a : R, a ∈ S → -a ∈ S → x * a ∈ S ∧ -(x * a) ∈ S where
  mp _ := by simpa [mem_supportAddSubgroup] using S.smul_mem_support
  mpr _ := ⟨by simpa [mem_supportAddSubgroup]⟩

instance [HasMemOrNegMem S] : S.HasIdealSupport where
  smul_mem_support x a ha :=
    match mem_or_neg_mem S x with
    | .inl hx => ⟨by simpa using mul_mem hx ha.1, by simpa using mul_mem hx ha.2⟩
    | .inr hx => ⟨by simpa using mul_mem hx ha.2, by simpa using mul_mem hx ha.1⟩

section support

variable [S.HasIdealSupport]

/--
The support of a subsemiring `S` of a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `P`.
-/
def support : Ideal R where
  __ := S.supportAddSubgroup
  smul_mem' := smul_mem_support S

variable {S} in
theorem mem_support {x} : x ∈ S.support ↔ x ∈ S ∧ -x ∈ S := .rfl

theorem coe_support : S.support = (S : Set R) ∩ -(S : Set R) := rfl

@[simp]
theorem supportAddSubgroup_eq : S.supportAddSubgroup = S.support.toAddSubgroup := rfl

end support

/-- A preordering on a ring `R` is a subsemiring of `R` containing all squares,
but not containing `-1`. -/
class IsPreordering {R : Type*} [i : CommRing R] (S : Subsemiring R) : Prop where
  mem_of_isSquare (S) {x} (hx : IsSquare x) : x ∈ S := by aesop
  neg_one_notMem (S) : -1 ∉ S := by aesop

export IsPreordering (mem_of_isSquare)
export IsPreordering (neg_one_notMem)

/- TODO : figure out how to make aesop fire when S.IsPreordering is an instance variable
          e.g. when we can see S.IsOrdering -/

@[aesop unsafe 20% forward (rule_sets := [SetLike])]
theorem neg_one_notMem' {_ : S.IsPreordering} : -1 ∉ S := S.neg_one_notMem

attribute [aesop unsafe 20% forward (rule_sets := [SetLike])] neg_one_notMem

section IsPreordering

variable [S.IsPreordering]

@[aesop unsafe 80% (rule_sets := [SetLike])]
protected theorem mem_of_isSumSq {x : R} (hx : IsSumSq x) : x ∈ S := by
  induction hx with
  | zero => simp
  | sq_add => aesop (add unsafe mem_of_isSquare)

theorem sumSq_le : .sumSq R ≤ S := fun _ ↦ by
  simpa using Subsemiring.mem_of_isSumSq S

@[simp]
protected theorem mul_self_mem (x : R) : x * x ∈ S := by aesop

@[simp]
protected theorem pow_two_mem (x : R) : x ^ 2 ∈ S := by aesop

end IsPreordering

/--
An ordering `O` on a ring `R` is a preordering such that
1. `O` contains either `x` or `-x` for each `x` in `R` and
2. the support of `O` is a prime ideal.
-/
class IsOrdering extends IsPreordering S, HasMemOrNegMem S, S.support.IsPrime

end Subsemiring
