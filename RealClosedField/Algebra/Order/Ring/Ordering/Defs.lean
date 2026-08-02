/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import RealClosedField.Algebra.Ring.Subsemiring.Support
import Mathlib.Algebra.Ring.SumsOfSquares
import Mathlib.Topology.Compactness.Compact

/-!
# Ring orderings

Let `R` be a commutative ring. We define orderings and preorderings on `R`
as predicates on `Subsemiring R`.

## Definitions

* `IsOrdering`: an ordering is a subsemiring `O` such that `O ∪ -O = R` and
the support `O ∩ -O` of `O` forms a prime ideal.
* `IsPreordering`: a preordering is a subsemiring that contains all squares, but not `-1`.

All orderings are preorderings.

## References

- [*An introduction to real algebra*, T.Y. Lam][lam_1984]

-/

namespace Subsemiring

variable {R : Type*} [CommRing R]

/--
An ordering `O` on a ring `R` is a subsemiring of `R` such that `O ∪ -O = R` and
the support `O ∩ -O` of `O` forms a prime ideal.
-/
structure IsOrdering (S : Subsemiring R) : Prop where
  isSpanning : S.IsSpanning
  support_ne_top : S.toAddSubmonoid.support ≠ ⊤
  mem_support_or_mem_support :
    ∀ {x y : R}, x * y ∈ S.toAddSubmonoid.support →
      x ∈ S.toAddSubmonoid.support ∨ y ∈ S.toAddSubmonoid.support

attribute [grind →] IsOrdering.isSpanning

namespace IsOrdering

@[simps!]
def supportIdeal {S : Subsemiring R} (hS : S.IsOrdering) : Ideal R where
  __ : AddSubgroup R := S.toAddSubmonoid.support
  smul_mem' x a ha := by
    have := hS.isSpanning.mem_or_neg_mem x
    have : ∀ x y, -x ∈ S → -y ∈ S → x * y ∈ S := fun _ _ hx hy ↦ by simpa using mul_mem hx hy
    aesop

@[simp]
theorem mem_supportIdeal {S : Subsemiring R} (hS : S.IsOrdering) (x : R) :
    x ∈ hS.supportIdeal ↔ x ∈ S.toAddSubmonoid.support := .rfl

@[simp]
theorem supportIdeal_toAddSubgroup {S : Subsemiring R} (hS : S.IsOrdering) :
    hS.supportIdeal.toAddSubgroup = S.toAddSubmonoid.support := rfl

theorem supportIdeal_isPrime {S : Subsemiring R} (hS : S.IsOrdering) :
    hS.supportIdeal.IsPrime where
  ne_top' := by
    apply_fun Submodule.toAddSubgroup
    simpa using hS.support_ne_top
  mem_or_mem' := hS.mem_support_or_mem_support

end IsOrdering

/-- A preordering on a ring `R` is a subsemiring of `R` that contains all squares, but not `-1`. -/
structure IsPreordering (S : Subsemiring R) : Prop where
  mem_of_isSquare (S) {x} (hx : IsSquare x) : x ∈ S := by grind
  neg_one_notMem (S) : -1 ∉ S := by grind

export IsPreordering (mem_of_isSquare)
export IsPreordering (neg_one_notMem)

attribute [grind →] neg_one_notMem

namespace IsPreordering

-- TODO : change to grind
@[aesop 80% (rule_sets := [SetLike]), grind ←]
protected theorem mem_of_isSumSq {S : Subsemiring R} (hS : IsPreordering S)
    {x : R} (hx : IsSumSq x) : x ∈ S := by
  induction hx with
  | zero => simp
  | sq_add => aesop (add unsafe mem_of_isSquare)

theorem sumSq_le {R : Type*} [CommRing R] {S : Subsemiring R} (hS : IsPreordering S) :
    Subsemiring.sumSq R ≤ S := fun _ ↦ by aesop

@[simp, grind ←]
protected theorem mul_self_mem {S : Subsemiring R} (hS : IsPreordering S) (x : R) :
    x * x ∈ S := by aesop

@[simp, grind ←]
protected theorem pow_two_mem {S : Subsemiring R} (hS : IsPreordering S) (x : R) :
    x ^ 2 ∈ S := by aesop

end IsPreordering

variable {S} in
theorem IsPreordering.of_ne_top
    {S : Subsemiring R} (hS : S.IsSpanning) (h : S ≠ ⊤) :
    S.IsPreordering where
  mem_of_isSquare x := by
    rcases x with ⟨y, rfl⟩
    cases S.mem_or_neg_mem hS y with
    | inl h => aesop
    | inr h => simpa using (show -y * -y ∈ S by aesop (config := { enableSimp := false }))
  neg_one_notMem hc := h <| by
    rw [Subsemiring.eq_top_iff']
    intro x
    rcases hS.mem_or_neg_mem x with (hx | hx)
    · simpa using hx
    · simpa using mul_mem hc hx

-- TODO : move to right place
@[simp]
theorem top_toSubmonoid :
    (⊤ : Subsemiring R).toSubmonoid = ⊤ := rfl

-- TODO : move to right place
@[simp]
theorem top_toAddSubmonoid :
    (⊤ : Subsemiring R).toAddSubmonoid = ⊤ := rfl

/- An ordering is a preordering. -/
theorem isPreordering_of_isOrdering {S : Subsemiring R} (hS : S.IsOrdering) : S.IsPreordering :=
    .of_ne_top hS.isSpanning <| fun hc ↦ by
  have := hS.supportIdeal_isPrime.ne_top
  apply_fun Submodule.toAddSubgroup at this
    using Submodule.toAddSubgroup_injective (R := R) (M := R)
  simp [hc] at this

end Subsemiring
