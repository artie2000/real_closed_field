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

variable {R : Type*} [CommRing R] {S : Type*} [SetLike S R] (s : S)

namespace AddSubmonoid

variable [AddSubmonoidClass S R]

/-!
#### Support
-/

section supportAddSubgroup

variable (s : AddSubmonoid R)

/--
The support of a subsemiring `S` of a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `S`.
-/
def supportAddSubgroup : AddSubgroup R where
  carrier := s ∩ -s
  zero_mem' := by aesop
  add_mem' := by aesop
  neg_mem' := by aesop

variable {s} in
theorem mem_supportAddSubgroup {x} : x ∈ s.supportAddSubgroup ↔ x ∈ s ∧ -x ∈ s := .rfl

theorem coe_supportAddSubgroup : s.supportAddSubgroup = (s ∩ -s : Set R) := rfl

end supportAddSubgroup

/-- Typeclass to track whether the support of a subsemiring forms an ideal. -/
class HasIdealSupport (s : S) : Prop where
  smul_mem_support (s) (x : R) {a : R} (ha : a ∈ (AddSubmonoid.ofClass s).supportAddSubgroup) :
    x * a ∈ (AddSubmonoid.ofClass s).supportAddSubgroup

export HasIdealSupport (smul_mem_support)

theorem hasIdealSupport_iff :
    HasIdealSupport s ↔ ∀ x a : R, a ∈ s → -a ∈ s → x * a ∈ s ∧ -(x * a) ∈ s where
  mp _ := by simpa [mem_supportAddSubgroup] using smul_mem_support (R := R) s
  mpr _ := ⟨by simpa [mem_supportAddSubgroup]⟩

section support

variable (s : AddSubmonoid R) [HasIdealSupport s]

/--
The support of a subsemiring `S` of a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `P`.
-/
def support : Ideal R where
  __ := supportAddSubgroup s
  smul_mem' := smul_mem_support s

variable {s} in
theorem mem_support {x} : x ∈ s.support ↔ x ∈ s ∧ -x ∈ s := .rfl

theorem coe_support : s.support = (s : Set R) ∩ -(s : Set R) := rfl

@[simp]
theorem supportAddSubgroup_eq : s.supportAddSubgroup = s.support.toAddSubgroup := rfl

end support

end AddSubmonoid

namespace Subsemiring

variable [SubsemiringClass S R]

instance [SubsemiringClass S R] [HasMemOrNegMem s] : AddSubmonoid.HasIdealSupport s where
  smul_mem_support x a ha :=
    match mem_or_neg_mem s x with
    | .inl hx => ⟨by simpa using mul_mem hx ha.1, by simpa using mul_mem hx ha.2⟩
    | .inr hx => ⟨by simpa using mul_mem hx ha.2, by simpa using mul_mem hx ha.1⟩

/-- A preordering on a ring `R` is a subsemiring of `R` containing all squares,
but not containing `-1`. -/
class IsPreordering [SubsemiringClass S R] (s : S) : Prop where
  mem_of_isSquare (s) {x} (hx : IsSquare x) : x ∈ s := by aesop
  neg_one_notMem (s) : -1 ∉ s := by aesop

export IsPreordering (mem_of_isSquare)
export IsPreordering (neg_one_notMem)

section IsPreordering

variable [IsPreordering s]

@[aesop unsafe 80% (rule_sets := [SetLike])]
protected theorem mem_of_isSumSq {x : R} (hx : IsSumSq x) : x ∈ s := by
  induction hx with
  | zero => simp
  | sq_add => aesop (add unsafe mem_of_isSquare)

theorem sumSq_le : Subsemiring.sumSq R ≤ .ofClass s := fun _ ↦ by
  simpa using Subsemiring.mem_of_isSumSq s

@[simp]
protected theorem mul_self_mem (x : R) : x * x ∈ s := by aesop

@[simp]
protected theorem pow_two_mem (x : R) : x ^ 2 ∈ s := by aesop

end IsPreordering

/--
An ordering `O` on a ring `R` is a preordering such that
1. `O` contains either `x` or `-x` for each `x` in `R` and
2. the support of `O` is a prime ideal.
-/
class IsOrdering extends IsPreordering s, HasMemOrNegMem s, (Subsemiring.ofClass s).support.IsPrime

end Subsemiring
