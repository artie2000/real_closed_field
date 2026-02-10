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

variable {K : Type*} [Field K] [IsAlgClosed K]
-- variable {R : Type*} [CommRing R] [IsDomain R] [Algebra K R]
variable {L : Type*} [Field L] [Algebra K L]

open IntermediateField in
example {x : L} (hx : IsAlgebraic K x) : ∃ y, algebraMap K L y = x := by
  have := isAlgebraic_adjoin_simple hx.isIntegral
  simpa [adjoin_eq_bot_iff, IntermediateField.mem_bot] using
    eq_bot_of_isAlgClosed_of_isAlgebraic K⟮x⟯
