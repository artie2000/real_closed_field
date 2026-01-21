import Mathlib

set_option trace.aesop true in
theorem test {R : Type*} [AddMonoid R] [Mul R]
    {a s : R} (ha : a ≠ 0)
    (ih : s ∈ AddSubsemigroup.closure {x | ∃ y, y ≠ 0 ∧ y * y = x}) :
    a * a + s ∈ AddSubsemigroup.closure {x | ∃ y, y ≠ 0 ∧ y * y = x} := by
  aesop

set_option trace.aesop true in
theorem works {R : Type*} [AddMonoid R] [Mul R]
    {a s : R} (ha : a ≠ 0)
    (ih : s ∈ AddSubsemigroup.closure {x | ∃ y, y ≠ 0 ∧ y * y = x}) :
    a * a + s ∈ AddSubsemigroup.closure {x | ∃ y, y ≠ 0 ∧ y * y = x} := by
  apply add_mem -- aesop safe apply 90%
  apply AddSubsemigroup.mem_closure_of_mem -- aesop safe apply 90%
  · aesop
  · aesop
