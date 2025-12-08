/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import Mathlib.Order.Zorn
import RealClosedField.Algebra.Order.Ring.Ordering.Basic

/-!

Let `R` be a commutative ring, and let `P` be a preordering on `R`. If `a ∉ P`, then we can extend
`P` to a preordering containing either `a` or `-a`.
Moreover, we can always extend `P` to an ordering on `R`.

We also prove various sufficient conditions to be able to extend `P` to `a`,
and that all orderings on a field are maximal preorderings.

## References

- [*An introduction to real algebra*, T.Y. Lam][lam_1984]

-/

/-!
### Adjoining an element to a preordering
-/

variable {R : Type*} [CommRing R] (P : IsPreordering R) (a : R)

namespace IsPreordering

theorem mem_subsemiringClosure_insert {x} :
    x ∈ Subsemiring.closure (insert a P) ↔ ∃ y ∈ P, ∃ z ∈ P, x = y + a * z where
  mp hx := by
    induction hx using Subsemiring.closure_induction with
    | mem x hx => cases hx
                  · exact ⟨0, by aesop, 1, by aesop, by simp_all⟩
                  · exact ⟨x, ‹_›, 0, by aesop, by simp⟩
    | zero => exact ⟨0, by aesop, 0, by aesop, by simp⟩
    | one => exact ⟨1, by aesop, 0, by aesop, by simp⟩
    | add _ _ _ _ ha hb =>
      rcases ha, hb with ⟨⟨x₁, hx₁, y₁, hy₁, rfl⟩, ⟨x₂, hx₂, y₂, hy₂, rfl⟩⟩
      exact ⟨x₁ + x₂, by aesop, y₁ + y₂, by aesop, by linear_combination⟩
    | mul _ _ _ _ ha hb =>
      rcases ha, hb with ⟨⟨x₁, hx₁, y₁, hy₁, rfl⟩, ⟨x₂, hx₂, y₂, hy₂, rfl⟩⟩
      exact ⟨x₁ * x₂ + (a * a) * (y₁ * y₂), by aesop, x₁ * y₂ + y₁ * x₂, by aesop,
        by linear_combination⟩
  mpr := by aesop

variable {P a} in
def adjoin (h : -1 ∉ Subsemiring.closure (insert a P)) : IsPreordering R where
  __ := Subsemiring.closure (insert a P)

variable {P a} in
@[aesop unsafe 90% apply (rule_sets := [SetLike])]
theorem mem_adjoin_of_mem (h : -1 ∉ Subsemiring.closure (insert a P)) {x : R} (hx : x ∈ P) :
    x ∈ adjoin h := Subsemiring.mem_closure_of_mem (by simp [hx])

variable {P a} in
theorem subset_adjoin (h : -1 ∉ Subsemiring.closure (insert a P)) : (P : Set R) ⊆ adjoin h :=
  fun _ => by aesop

variable {P a} in
@[aesop safe apply (rule_sets := [SetLike])]
theorem self_mem_adjoin (h : -1 ∉ Subsemiring.closure (insert a P)) : a ∈ adjoin h :=
  Subsemiring.mem_closure_of_mem (by simp)

/-
### Sufficient conditions for adjoining an element
-/

variable {P} in
theorem neg_one_notMem_adjoin_or_of_neg_mul_mem {x y : R} (h : -(x * y) ∈ P) :
    -1 ∉ Subsemiring.closure (insert x P) ∨ -1 ∉ Subsemiring.closure (insert y P) := by
  rw [mem_subsemiringClosure_insert]
  by_contra
  apply IsPreordering.neg_one_notMem P
  rcases (mem_subsemiringClosure_insert P x).mp (show -1 ∈ _ by aesop)
    with ⟨s₁, hs₁, s₂, hs₂, eqx⟩
  rcases (mem_subsemiringClosure_insert P y).mp (show -1 ∈ _ by aesop)
    with ⟨t₁, ht₁, t₂, ht₂, eqy⟩
  rw [show -1 = (-(x * y)) * s₂ * t₂ + s₁ + t₁ + (s₁ * t₁) by
    linear_combination (t₁ + 1) * eqx - 1 * x * s₂ * eqy]
  aesop (config := { enableSimp := false })

theorem neg_one_notMem_adjoin_or :
    -1 ∉ Subsemiring.closure (insert a P) ∨ -1 ∉ Subsemiring.closure (insert (-a) P) :=
  neg_one_notMem_adjoin_or_of_neg_mul_mem (by simp_all : -(a * (- a)) ∈ P)

theorem neg_one_notMem_adjoin
    (h : ∀ x y, x ∈ P → y ∈ P → x + (1 + y) * a + 1 ≠ 0) :
    -1 ∉ Subsemiring.closure (insert a P) := fun _ => by
  rcases (mem_subsemiringClosure_insert P a).mp
           (show -1 * (1 + a) ∈ _ by aesop (erase simp neg_mul)) with ⟨x, hx, y, hy, eqn⟩
  exact h _ _ hx hy (by linear_combination - eqn)

/--
If `F` is a field, `P` is a preordering on `F`, and `a` is an element of `P` such that `-a ∉ P`,
then `-1` is not of the form `x + a * y` with `x` and `y` in `P`.
-/
theorem neg_one_notMem_adjoin_of_neg_notMem
    {F : Type*} [Field F] {P : IsPreordering F} {a : F}
    (ha : -a ∉ P) : -1 ∉ Subsemiring.closure (insert a P) := by
  rw [mem_subsemiringClosure_insert]
  rintro ⟨x, hx, y, hy, eqn⟩
  apply ha
  have : y ≠ 0 := fun _ => by aesop
  rw [show -a = x * y⁻¹ + y⁻¹ by field_simp; linear_combination eqn]
  aesop

/-!
### Existence of orderings
-/

theorem exists_le :
    ∃ Q : IsPreordering R, P ≤ Q ∧ (a ∈ Q ∨ -a ∈ Q) := by
  cases neg_one_notMem_adjoin_or P a with
  | inl h => exact ⟨adjoin h, subset_adjoin _, by aesop⟩
  | inr h => exact ⟨adjoin h, subset_adjoin _, by aesop⟩

theorem exists_lt (hp : a ∉ P) (hn : -a ∉ P) :
    ∃ Q : IsPreordering R, P < Q := by
  rcases exists_le P a with ⟨Q, le, p_mem | n_mem⟩
  · exact ⟨Q, lt_of_le_of_ne le <| Ne.symm (ne_of_mem_of_not_mem' p_mem hp)⟩
  · exact ⟨Q, lt_of_le_of_ne le <| Ne.symm (ne_of_mem_of_not_mem' n_mem hn)⟩

/- A maximal preordering on `R` is an ordering. -/
theorem isOrdering_of_maximal {O : IsPreordering R} (max : IsMax O) :
    O.IsOrdering := isOrdering_iff.mpr <| fun a b h => by
  cases neg_one_notMem_adjoin_or_of_neg_mul_mem h with
  | inl h => exact Or.inl <| max (subset_adjoin h) (self_mem_adjoin h)
  | inr h => exact Or.inr <| max (subset_adjoin h) (self_mem_adjoin h)

/- Every preordering on `R` extends to an ordering. -/
theorem exists_le_isOrdering :
    ∃ O : IsPreordering R, P ≤ O ∧ O.IsOrdering := by
  have := P.isSemireal
  have ⟨_, _, hO⟩ : ∃ O, P ≤ O ∧ IsMax O := by
    refine zorn_le_nonempty_Ici₀ _ (fun _ _ hc _ hQ => ?_) _ le_rfl
    simp_all [← bddAbove_def, (CompletePartialOrder.lubOfDirected _ hc.directedOn).bddAbove]
  exact ⟨_, by assumption, isOrdering_of_maximal hO⟩

/- An ordering on `R` is maximal among preorderings iff it is maximal among orderings. -/
theorem maximal_iff_maximal_isOrdering {O : IsPreordering R} [O.IsOrdering] :
    IsMax O ↔ Maximal IsPreordering.IsOrdering O :=
  ⟨fun h => Maximal.mono (by simpa using h) (fun _ _ => trivial) inferInstance,
   fun hO P le₁ => by aesop (add safe forward exists_le_isOrdering,
                                 safe forward le_trans,
                                 safe forward Maximal.eq_of_ge)⟩

/-!
### Comparison of orderings
-/

variable {P a}

def HasMemOrNegMem_of_ge [HasMemOrNegMem P] {Q : IsPreordering R}
    (h : P ≤ Q) : HasMemOrNegMem Q where
  mem_or_neg_mem a := have := mem_or_neg_mem P a; by aesop

theorem mem_support_of_ge_of_notMem [HasMemOrNegMem P] {Q : IsPreordering R}
    (h : P ≤ Q) (ha : a ∈ Q) (haP : a ∉ P) :
    let := HasMemOrNegMem_of_ge h
    a ∈ Q.support := by
  aesop (add simp mem_support)

theorem eq_of_le_of_supportAddSubgroup_eq_bot {P} [HasMemOrNegMem P] {Q : IsPreordering R}
    (h : P ≤ Q) (hSupp : let := HasMemOrNegMem_of_ge h; Q.support = ⊥) : P = Q := by
  by_contra h2
  have ⟨x, hx, hx2⟩ : ∃ x, x ∈ Q ∧ x ∉ P :=
    Set.exists_of_ssubset <| lt_of_le_of_ne h (by simpa using h2)
  have : -x ∈ Q := by aesop
  apply_fun (x ∈ ·) at hSupp
  aesop (add simp mem_support)

theorem eq_of_le {F : Type*} [Field F] {P Q : IsPreordering F} [P.IsOrdering] (h : P ≤ Q) :
    P = Q := eq_of_le_of_supportAddSubgroup_eq_bot h (support_eq_bot Q)

/- A preordering on a field `F` is maximal iff it is an ordering. -/
theorem maximal_iff_isOrdering {F : Type*} [Field F] {O : IsPreordering F} :
    IsMax O ↔ O.IsOrdering where
  mp h := have := isOrdering_of_maximal h; inferInstance
  mpr _ _ le := le_of_eq (eq_of_le le).symm
