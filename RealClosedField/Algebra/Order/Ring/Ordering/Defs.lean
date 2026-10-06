import RealClosedField.Upstream
import Mathlib.Algebra.Order.Ring.Ordering.Defs

namespace Subsemiring

variable {R : Type*} [CommRing R]

-- TODO : membership tag on definition of support

/--
An ordering `O` on a ring `R` is a subsemiring of `R` such that `O ∪ -O = R` and
the support `O ∩ -O` of `O` forms a prime ideal.
-/
structure IsOrdering (S : Subsemiring R) : Prop where
  isSpanning : S.IsSpanning
  support_ne_top : S.support ≠ ⊤
  mem_support_or_mem_support :
    ∀ {x y : R}, x * y ∈ S.support →
      x ∈ S.support ∨ y ∈ S.support

theorem IsOrdering.isPrime_supportIdeal {S : Subsemiring R} (hS : S.IsOrdering) :
    (S.supportIdeal hS.isSpanning).IsPrime where
  ne_top' := by
    apply_fun Submodule.toAddSubgroup
    simpa using hS.support_ne_top
  mem_or_mem' := hS.mem_support_or_mem_support

theorem IsOrdering.of_isPrime_supportIdeal {S : Subsemiring R} (hS : S.IsSpanning)
    (hS₂ : (S.supportIdeal hS).IsPrime) : S.IsOrdering where
  isSpanning := hS
  support_ne_top := by simpa [← Submodule.toAddSubgroup_inj] using hS₂.ne_top
  mem_support_or_mem_support := hS₂.mem_or_mem

/-- A preordering on a ring `R` is a subsemiring of `R` that contains all squares, but not `-1`. -/
structure IsPreordering (S : Subsemiring R) : Prop where
  mem_of_isSquare (S) {x} (hx : IsSquare x) : x ∈ S := by grind -- by membership
  neg_one_notMem (S) : -1 ∉ S := by grind -- by membership

export IsPreordering (mem_of_isSquare)
export IsPreordering (neg_one_notMem)

namespace IsPreordering

-- TODO : membership tag
protected theorem mem_of_isSumSq {S : Subsemiring R} (hS : IsPreordering S)
    {x : R} (hx : IsSumSq x) : x ∈ S := by
  induction hx with
  | zero => simp
  | sq_add => grind [mem_of_isSquare, IsSquare, add_mem]

theorem sumSq_le {R : Type*} [CommRing R] {S : Subsemiring R} (hS : IsPreordering S) :
    Subsemiring.sumSq R ≤ S := fun _ ↦ by simp_all [Subsemiring.IsPreordering.mem_of_isSumSq]

-- TODO : membership tag
@[simp]
protected theorem mul_self_mem {S : Subsemiring R} (hS : IsPreordering S) (x : R) :
    x * x ∈ S := by simp_all [Subsemiring.IsPreordering.mem_of_isSumSq]

-- TODO : membership tag
@[simp]
protected theorem pow_two_mem {S : Subsemiring R} (hS : IsPreordering S) (x : R) :
    x ^ 2 ∈ S := by simpa [pow_two] using Subsemiring.IsPreordering.mul_self_mem hS x

end IsPreordering

variable {S} in
theorem IsPreordering.of_ne_top {S : Subsemiring R} (hS : S.IsSpanning) (h : S ≠ ⊤) :
    S.IsPreordering := by
  rw [Subsemiring.isSpanning_def] at hS
  refine ⟨fun x ↦ ?_, fun hc ↦ h ?_⟩
  · rcases x with ⟨y, rfl⟩
    rcases hS y with hy | hy
    · exact mul_mem hy hy
    · simpa using mul_mem hy hy
  · rw [eq_top_iff]
    intro x
    rcases hS x with hx | hx
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
theorem IsOrdering.isPreordering {S : Subsemiring R} (hS : S.IsOrdering) : S.IsPreordering :=
    .of_ne_top hS.isSpanning <| fun hc ↦ by
  have := hS.isPrime_supportIdeal.ne_top
  apply_fun Submodule.toAddSubgroup at this
    using Submodule.toAddSubgroup_injective (R := R) (M := R)
  simp [hc] at this

end Subsemiring
