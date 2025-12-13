/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import RealClosedField.Algebra.Group.Submonoid.Support
import Mathlib.Algebra.Ring.SumsOfSquares

/-!
# Ring orderings

Let `R` be a commutative ring. We define orderings and preorderings on `R`
as predicates on `Subsemiring R`.

## Definitions

* `IsOrdering`: an ordering is a subsemiring `O` such that `O ∪ -O = R` and
the support `O ∩ -O` of `O` forms a prime ideal.
* `IsPreordering`: a preordering is a subsemiring that contains all squares, but not `-1`.

All orderings are preorderings.

An ordering `O` with support `p` makes `R⧸p` a totally ordered ring
with `O` as the set of non-negative elements. See `Algebra.Order.Ring.Ordering.Order`.

## References

- *An introduction to real algebra*, by T.Y. Lam. Rocky Mountain J. Math. 14(4): 767-814 (1984).
[lam_1984](https://doi.org/10.1216/RMJ-1984-14-4-767)

-/

namespace Subsemiring

variable {R : Type*} [Ring R] (S : Subsemiring R)

/--
An ordering `O` on a ring `R` is a subsemiring of `R` such that `O ∪ -O = R` and
the support `O ∩ -O` of `O` forms a prime ideal.
-/
class IsOrdering extends S.HasMemOrNegMem, S.support.IsPrime

/-- A preordering on a ring `R` is a subsemiring of `R` that contains all squares, but not `-1`. -/
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

/- An ordering is a preordering. -/
instance [S.IsOrdering] : S.IsPreordering :=
  .of_support_neq_top (Ideal.IsPrime.ne_top inferInstance)

end Subsemiring
