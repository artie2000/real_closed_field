/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Subsemiring.Basic
import RealClosedField.Mathlib.Algebra.Group.Even
import RealClosedField.Mathlib.Algebra.Group.Submonoid.Membership

/-!
# Sums of squares

We introduce sums of squares in a type `R` endowed with an `[Add R]`, `[Zero R]` and `[Mul R]`
instances. Sums of squares in `R` are defined by an inductive predicate `IsSumSq : R → Prop`:
`0 : R` is a sum of squares and if `S` is a sum of squares, then for all `a : R`, `a * a + S` is a
sum of squares in `R`.

## Declarations

- The predicate `IsSumSq : R → Prop`, defining the property of being a sum of squares in `R`.
- The terms `AddMonoid.sumSqIn R` and `Subsemiring.sumSqIn R` :
in an additive monoid with multiplication `R` and a semiring `R`, we introduce the terms
`AddMonoid.sumSqIn R` and `Subsemiring.sumSqIn R` as the submonoid and subsemiring, respectively,
of `R` whose carrier is the subset `{S : R | IsSumSq S}`.

-/

universe u
variable {R : Type*}

/--
In a type `R` with an addition, a zero element and a multiplication, the property of being a sum of
squares is defined by an inductive predicate: `0 : R` is a sum of squares and if `S` is a sum of
squares, then for all `a : R`, `a * a + S` is a sum of squares in `R`.
-/
@[mk_iff]
inductive IsSumSq [Mul R] [Add R] [Zero R] : R → Prop
  | zero                              : IsSumSq 0
  | sq_add {a S : R} (hS : IsSumSq S) : IsSumSq (a * a + S)

@[deprecated (since := "2024-08-09")] alias isSumSq := IsSumSq

/-- Alternative induction scheme for `IsSumSq` using `IsSquare`. -/
theorem IsSumSq.induction_alt [Mul R] [Add R] [Zero R]
    {p : (S : R) → (h : IsSumSq S) → Prop} (S : R) (hS : IsSumSq S)
    (zero : p 0 zero)
    (sq_add : ∀ {x S}, (hS : IsSumSq S) → (hx : IsSquare x) → p S hS →
      p (x + S) (by obtain ⟨y, rfl⟩ := hx; exact sq_add hS)) : p S hS := by
  induction hS with
  | zero            => exact zero
  | sq_add hS hS_ih => exact sq_add hS (.mul_self _) hS_ih

/-- In an additive monoid with multiplication,
if `S1` and `S2` are sums of squares, then `S1 + S2` is a sum of squares. -/
@[aesop safe apply]
theorem IsSumSq.add [AddMonoid R] [Mul R] {S1 S2 : R}
    (h1 : IsSumSq S1) (h2 : IsSumSq S2) : IsSumSq (S1 + S2) := by
  induction h1 with
  | zero        => simp [zero_add, h2]
  | sq_add _ ih => simp [add_assoc, sq_add, ih]

@[deprecated (since := "2024-08-09")] alias isSumSq.add := IsSumSq.add

namespace AddSubmonoid
variable {T : Type*} [AddMonoid T] [Mul T] {a : T}

variable (T) in
/--
In an additive monoid with multiplication `R`, the type `AddSubmonoid.sumSqIn R`
is the submonoid of sums of squares in `R`.
-/
def sumSqIn : AddSubmonoid T where
  carrier := {S : T | IsSumSq S}
  zero_mem' := IsSumSq.zero
  add_mem' := IsSumSq.add

@[simp] lemma mem_sumSqIn : a ∈ sumSqIn T ↔ IsSumSq a := Iff.rfl
@[simp, norm_cast] lemma coe_sumSqIn : sumSqIn T = {x : T | IsSumSq x} := rfl

end AddSubmonoid

/-- In an additive, commutative monoid with multiplication, a finite sum of sums of squares
is a sum of squares. -/
theorem IsSumSq.sum [AddCommMonoid R] [Mul R] {ι : Type*} {I : Finset ι} {S : ι → R}
    (hS : ∀ i ∈ I, IsSumSq <| S i) : IsSumSq (∑ i ∈ I, S i) := by
  simpa using sum_mem (S := AddSubmonoid.sumSqIn R) hS

/-- In an additive unital magma with multiplication, `x * x` is a sum of squares for all `x`. -/
theorem IsSumSq.mul_self [AddZeroClass R] [Mul R] (a : R) : IsSumSq (a * a) := by
  rw [← add_zero (a * a)]; exact sq_add zero

/-- In an additive unital magma with multiplication `R`, squares in `R` are sums of squares.
By definition, a square in `R` is a term `x : R` such that `x = y * y` for some `y : R`
and in Mathlib this is known as `IsSquare R` (see Mathlib.Algebra.Group.Even). -/
@[aesop unsafe apply]
theorem IsSquare.isSumSq [AddZeroClass R] [Mul R] {x : R} (hx : IsSquare x) :
    IsSumSq x := by obtain ⟨_, rfl⟩ := hx; exact IsSumSq.mul_self _

/--
In an additive monoid with multiplication `R`, the submonoid generated by the squares is the set of
sums of squares in `R`.
-/
@[simp] theorem AddSubmonoid.closure_isSquare [AddMonoid R] [Mul R] :
    closure {x : R | IsSquare x} = sumSqIn R := by
  refine closure_eq_of_le (fun x hx ↦ IsSquare.isSumSq hx) (fun x hx ↦ ?_)
  induction hx with
  | zero         => exact zero_mem _
  | sq_add _ ih  => exact add_mem (subset_closure (.mul_self _)) ih

@[deprecated (since := "2024-08-09")] alias SquaresAddClosure := AddSubmonoid.closure_isSquare

/-- A term of the form `∑ i ∈ I, x i * x i` satisfies `IsSumSq`. -/
@[aesop safe apply]
theorem IsSumSq.sum_mul_self [AddCommMonoid R] [Mul R]
    {ι : Type*} {I : Finset ι} (x : ι → R) : IsSumSq (∑ i ∈ I, x i * x i) := by
  simpa using sum_mem (S := AddSubmonoid.sumSqIn R) (by aesop)

/-- A term of `R` satisfying `IsSumSq` can be written as `∑ i ∈ I, x i * x i`. -/
theorem exists_sum_of_isSumSq [AddCommMonoid R] [Mul R] {a : R} (ha : IsSumSq a) :
    (∃ (ι : Type) (I : Finset ι) (x : ι → R), a = ∑ i ∈ I, x i * x i) := by
  obtain ⟨_, I, _, y_cl, rfl⟩ :=
    AddSubmonoid.exists_finset_sum_of_mem_closure (s := {x : R | IsSquare x}) (by simpa)
  choose! x hx using y_cl
  exact ⟨_, I, x, Finset.sum_equiv (by rfl) (by simp) hx⟩

/-- Universe-polymorphic version of `exists_sum_of_isSumSq`. -/
theorem exists_sum_of_isSumSq' [AddCommMonoid R] [Mul R] {a : R} (ha : IsSumSq a) :
    (∃ (ι : Type u) (I : Finset ι) (x : ι → R), a = ∑ i ∈ I, x i * x i) := by
  obtain ⟨ι, I, x, _⟩ := exists_sum_of_isSumSq ha
  exact ⟨ULift.{u} ι, .map (Equiv.ulift.symm.toEmbedding) I, x ∘ (Equiv.ulift.toEmbedding),
    by simpa⟩

/-- A term of `R` satisfies `IsSumSq` if and only if it can be written as `∑ i ∈ I, x i * x i`. -/
theorem isSumSq_iff_exists_sum [AddCommMonoid R] [Mul R] (a : R) :
    IsSumSq a ↔
    (∃ (ι : Type) (I : Finset ι) (x : ι → R), a = ∑ i ∈ I, x i * x i) := by
  refine ⟨exists_sum_of_isSumSq, by rintro ⟨_, _, _, rfl⟩; exact IsSumSq.sum_mul_self _⟩

/-- In a (not necessarily unital) commutative semiring,
if `S1` and `S2` are sums of squares, then `S1 * S2` is a sum of squares. -/
@[aesop unsafe 50% apply]
theorem IsSumSq.mul [NonUnitalCommSemiring R] {S1 S2 : R}
    (h1 : IsSumSq S1) (h2 : IsSumSq S2) : IsSumSq (S1 * S2) := by
  rw [isSumSq_iff_exists_sum] at *
  obtain ⟨ι, I, x, rfl⟩ := h1; obtain ⟨β, J, y, rfl⟩ := h2
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine ⟨_, I ×ˢ J, fun ⟨i,j⟩ => x i * y j, ?_⟩
  simp [mul_assoc, mul_comm, mul_left_comm]

namespace Subsemiring
variable {T : Type*} [CommSemiring T] {a : T}

variable (T) in
/--
In a commutative semiring `R`, the type `Subsemiring.sumSqIn R`
is the subsemiring of sums of squares in `R`.
-/
def sumSqIn : Subsemiring T where
  __ := AddSubmonoid.sumSqIn T
  mul_mem' := IsSumSq.mul
  one_mem' := IsSquare.isSumSq isSquare_one

@[simp] lemma sumSqIn_toAddSubmonoid : (sumSqIn T).toAddSubmonoid = .sumSqIn T := rfl
@[simp] lemma mem_sumSqIn : a ∈ sumSqIn T ↔ IsSumSq a := Iff.rfl
@[simp, norm_cast] lemma coe_sumSqIn : sumSqIn T = {x : T | IsSumSq x} := rfl

end Subsemiring

/-- In a commutative semiring, a finite product of sums of squares
is a sum of squares. -/
theorem IsSumSq.prod [CommSemiring R] {ι : Type*} {I : Finset ι} {f : ι → R}
    (hf : ∀ i ∈ I, IsSumSq <| f i) : IsSumSq (∏ i ∈ I, f i) := by
  simpa using prod_mem (S := Subsemiring.sumSqIn R) hf

/--
In a commutative semiring `R`, the subsemiring generated by the squares is the set of
sums of squares in `R`.
-/
@[simp] theorem Subsemiring.closure_isSquare [CommSemiring R] :
    closure {x : R | IsSquare x} = sumSqIn R := by
  refine closure_eq_of_le (fun x hx => IsSquare.isSumSq hx) (fun x hx ↦ ?_)
  obtain ⟨ι, I, y, hy⟩ := exists_sum_of_isSumSq (by simpa using hx)
  simpa [hy] using sum_mem (fun i _ => by apply subset_closure; simp)

/--
Let `R` be a linearly ordered semiring in which the property `a ≤ b → ∃ c, a + c = b` holds
(e.g. `R = ℕ`). If `S : R` is a sum of squares in `R`, then `0 ≤ S`. This is used in
`Mathlib.Algebra.Ring.Semireal.Defs` to show that such semirings are semireal.
-/
theorem IsSumSq.nonneg {R : Type*} [LinearOrderedSemiring R] [ExistsAddOfLE R] {S : R}
    (pS : IsSumSq S) : 0 ≤ S := by
  obtain ⟨ι, I, x, rfl⟩ := exists_sum_of_isSumSq pS
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg <| x i)

@[deprecated (since := "2024-08-09")] alias isSumSq.nonneg := IsSumSq.nonneg
