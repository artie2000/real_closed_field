/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.Algebra.Algebra.Subalgebra.Unitization

/-!
# Sums of squares

We introduce a predicate for sums of squares in a ring.

## Main declarations

- The predicate `IsSumSq : R → Prop`: for a type `R` with addition, multiplication and a zero.,
an inductive predicate defining the property of being a sum of squares in `R`.
`0 : R` is a sum of squares and if `S` is a sum of squares, then, for all `a : R`, `a * a + s` is a
sum of squares.
- The terms `AddMonoid.sumSq R` and `Subsemiring.sumSq R`: respectively
the submonoid and subsemiring of sums of squares in the corresponding structure `R`.

-/

universe u
variable {R : Type*}

/--
The property of being a sum of squares is defined inductively by:
`0 : R` is a sum of squares and if `s : R` is a sum of squares,
then for all `a : R`, `a * a + s` is a sum of squares in `R`.
-/
@[mk_iff]
inductive IsSumSq [Mul R] [Add R] [Zero R] : R → Prop
  | zero                              : IsSumSq 0
  | sq_add {a s : R} (hs : IsSumSq s) : IsSumSq (a * a + s)

@[deprecated (since := "2024-08-09")] alias isSumSq := IsSumSq

/-- Alternative induction scheme for `IsSumSq` which uses `IsSquare`. -/
theorem IsSumSq.rec' [Mul R] [Add R] [Zero R]
    {motive : (s : R) → (h : IsSumSq s) → Prop}
    (zero : motive 0 zero)
    (sq_add : ∀ {x s}, (hx : IsSquare x) → (hs : IsSumSq s) → motive s hs →
      motive (x + s) (by rcases hx with ⟨_, rfl⟩; exact sq_add hs))
    {s : R} (h : IsSumSq s) : motive s h :=
  match h with
  | .zero      => zero
  | .sq_add ih => sq_add (.mul_self _) ih (rec' zero sq_add _)

/-- In an additive monoid with multiplication,
if `s₁` and `s₂` are sums of squares, then `s₁ + s₂` is a sum of squares. -/
@[aesop unsafe 90% apply]
theorem IsSumSq.add [AddMonoid R] [Mul R] {s₁ s₂ : R}
    (h₁ : IsSumSq s₁) (h₂ : IsSumSq s₂) : IsSumSq (s₁ + s₂) := by
  induction h₁ with
  | zero        => simp_all
  | sq_add _ ih => simp_all [add_assoc, sq_add]

@[deprecated (since := "2024-08-09")] alias isSumSq.add := IsSumSq.add

namespace AddSubmonoid
variable {T : Type*} [AddMonoid T] [Mul T] {s : T}

variable (T) in
/--
In an additive monoid with multiplication `R`, `AddSubmonoid.sumSq R`
is the submonoid of sums of squares in `R`.
-/
def sumSq : AddSubmonoid T where
  carrier := {s : T | IsSumSq s}
  zero_mem' := .zero
  add_mem' := .add

@[simp] theorem mem_sumSq : s ∈ sumSq T ↔ IsSumSq s := Iff.rfl
@[simp, norm_cast] theorem coe_sumSq : sumSq T = {s : T | IsSumSq s} := rfl

end AddSubmonoid

/-- In an additive unital magma with multiplication, `x * x` is a sum of squares for all `x`. -/
@[aesop safe apply]
theorem IsSumSq.mul_self [AddZeroClass R] [Mul R] (a : R) : IsSumSq (a * a) := by
  rw [← add_zero (a * a)]; exact sq_add zero

/-- In an additive unital magma with multiplication, squares are sums of squares
(see Mathlib.Algebra.Group.Even.Basic). -/
@[aesop unsafe 50% apply]
theorem IsSquare.isSumSq [AddZeroClass R] [Mul R] {x : R} (hx : IsSquare x) :
    IsSumSq x := by rcases hx with ⟨_, rfl⟩; apply IsSumSq.mul_self

/--
In an additive monoid with multiplication `R`, the submonoid generated by the squares is the set of
sums of squares in `R`.
-/
@[simp]
theorem AddSubmonoid.closure_isSquare [AddMonoid R] [Mul R] :
    closure {x : R | IsSquare x} = sumSq R := by
  refine closure_eq_of_le (fun x hx ↦ IsSquare.isSumSq hx) (fun x hx ↦ ?_)
  induction hx with
  | zero         => exact zero_mem _
  | sq_add _ ih  => exact add_mem (subset_closure (.mul_self _)) ih

@[deprecated (since := "2024-08-09")] alias SquaresAddClosure := AddSubmonoid.closure_isSquare

/-- In an additive, commutative monoid with multiplication, a finite sum of sums of squares
is a sum of squares. -/
@[aesop unsafe 90% apply]
theorem IsSumSq.sum [AddCommMonoid R] [Mul R] {ι : Type*} {I : Finset ι} {s : ι → R}
    (hs : ∀ i ∈ I, IsSumSq <| s i) : IsSumSq (∑ i ∈ I, s i) := by
  simpa using sum_mem (S := AddSubmonoid.sumSq R) hs

/-- In an additive, commutative monoid with multiplication,
a term of the form `∑ i ∈ I, x i`, where each `x i` is a square, is a sum of squares. -/
@[aesop unsafe 50% apply]
theorem IsSumSq.sum_isSquare [AddCommMonoid R] [Mul R] {ι : Type*} (I : Finset ι) {x : ι → R}
    (ha : ∀ i ∈ I, IsSquare <| x i) :
    IsSumSq (∑ i ∈ I, x i) := by aesop

/-- In an additive, commutative monoid with multiplication,
a term of the form `∑ i ∈ I, a i * a i` is a sum of squares. -/
@[aesop safe apply]
theorem IsSumSq.sum_mul_self [AddCommMonoid R] [Mul R] {ι : Type*} (I : Finset ι) (a : ι → R) :
    IsSumSq (∑ i ∈ I, a i * a i) := by aesop

@[deprecated (since := "2024-12-23")] alias isSumSq_sum_mul_self := IsSumSq.sum_mul_self

namespace NonUnitalSubsemiring
variable {T : Type*} [NonUnitalCommSemiring T] {s : T}

variable (T) in
/--
In a commutative (possibly non-unital) semiring `R`, `NonUnitalSubsemiring.sumSq R` is
the (possibly non-unital) subsemiring of sums of squares in `R`.
-/
def sumSq : NonUnitalSubsemiring T := (Subsemigroup.squareIn T).nonUnitalSubsemiringClosure

@[simp] theorem sumSq_toAddSubmonoid : (sumSq T).toAddSubmonoid = .sumSq T := by
  rw [sumSq, ← AddSubmonoid.closure_isSquare,
    Subsemigroup.nonUnitalSubsemiringClosure_toAddSubmonoid]
  simp

@[simp]
theorem mem_sumSq : s ∈ sumSq T ↔ IsSumSq s := by
  rw [← NonUnitalSubsemiring.mem_toAddSubmonoid]; simp

@[simp, norm_cast] theorem coe_sumSq : sumSq T = {s : T | IsSumSq s} := by ext; simp

@[simp] theorem closure_isSquare : closure {x : T | IsSquare x} = sumSq T := by
  rw [sumSq, Subsemigroup.nonUnitalSubsemiringClosure_eq_closure]
  simp

end NonUnitalSubsemiring

/-- In a commutative (possibly non-unital) semiring,
if `s₁` and `s₂` are sums of squares, then `s₁ * s₂` is a sum of squares. -/
@[aesop unsafe 50% apply]
theorem IsSumSq.mul [NonUnitalCommSemiring R] {s₁ s₂ : R}
    (h₁ : IsSumSq s₁) (h₂ : IsSumSq s₂) : IsSumSq (s₁ * s₂) := by
  simpa using mul_mem (by simpa : _ ∈ NonUnitalSubsemiring.sumSq R) (by simpa)

private theorem Submonoid.square_subsemiringClosure {T : Type*} [CommSemiring T] :
    (Submonoid.squareIn T).subsemiringClosure = .closure {x : T | IsSquare x} := by
  simp [Submonoid.subsemiringClosure_eq_closure]

namespace Subsemiring
variable {T : Type*} [CommSemiring T] {s : T}

variable (T) in
/--
In a commutative semiring `R`, `Subsemiring.sumSq R` is the subsemiring of sums of squares in `R`.
-/
def sumSq : Subsemiring T where
  __ := NonUnitalSubsemiring.sumSq T
  one_mem' := by aesop

@[simp] theorem sumSq_toNonUnitalSubsemiring :
    (sumSq T).toNonUnitalSubsemiring = .sumSq T := rfl

@[simp]
theorem mem_sumSq : s ∈ sumSq T ↔ IsSumSq s := by
  rw [← Subsemiring.mem_toNonUnitalSubsemiring]; simp

@[simp, norm_cast] theorem coe_sumSq : sumSq T = {s : T | IsSumSq s} := by ext; simp

@[simp] theorem closure_isSquare : closure {x : T | IsSquare x} = sumSq T := by
  apply_fun toNonUnitalSubsemiring using toNonUnitalSubsemiring_injective
  simp [← Submonoid.square_subsemiringClosure]

end Subsemiring

/-- In a commutative semiring, a finite product of sums of squares is a sum of squares. -/
@[aesop unsafe 50% apply]
theorem IsSumSq.prod [CommSemiring R] {ι : Type*} {I : Finset ι} {x : ι → R}
    (hx : ∀ i ∈ I, IsSumSq <| x i) : IsSumSq (∏ i ∈ I, x i) := by
  simpa using prod_mem (S := Subsemiring.sumSq R) (by simpa)

/--
In a linearly ordered semiring with the property `a ≤ b → ∃ c, a + c = b` (e.g. `ℕ`),
sums of squares are non-negative.
-/
theorem IsSumSq.nonneg {R : Type*} [LinearOrderedSemiring R] [ExistsAddOfLE R] {s : R}
    (ps : IsSumSq s) : 0 ≤ s := by
  induction ps using IsSumSq.rec'
  case zero => aesop
  case sq_add x s hx hs h_sum => exact add_nonneg (IsSquare.nonneg hx) h_sum

@[deprecated (since := "2024-08-09")] alias isSumSq.nonneg := IsSumSq.nonneg
