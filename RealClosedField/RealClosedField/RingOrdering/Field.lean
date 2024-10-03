/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/

import RealClosedField.RealClosedField.RingOrdering.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Order.Zorn

@[aesop safe apply (rule_sets := [SetLike])]
theorem RingPreordering.inv_mem
    {S F : Type*} [Field F] [SetLike S F] [RingPreorderingClass S F] {P : S} {a : F}
    (ha : a ∈ P) : a⁻¹ ∈ P := by
  rw [(by field_simp : a⁻¹ = a * (a⁻¹ * a⁻¹))]
  aesop

section adjoin_field

variable {S F : Type*} [Field F] [SetLike S F] [RingPreorderingClass S F] (P : S)

/- set_option trace.aesop true -/

/--
If `F` is a field, `P` is a preordering on `F`, and `a` is an element of `P` such that `-a ∉ P`,
then `-1` is not of the form `x + a * y` for any `x` and `y` in `P`.
This is the crucial fact that allows preorderings to be extended by unordered elements.
-/
theorem RingPreordering.minus_one_not_mem_adjoin_linear
    (a : F) (ha : -a ∉ P) (x y : F) (hx : x ∈ P) (hy : y ∈ P) :
    -1 ≠ x + a * y := by
  intro hz
  apply ha
  have : y ≠ 0 := fun _ => by simpa [*] using minus_one_not_mem P
  rw [show -a = x * y⁻¹ + y⁻¹ by
    field_simp
    rw [neg_eq_iff_eq_neg.mp hz]
    ring]
  aesop

/-
If `F` is a field, `P` is a preordering on `F`, and `a` in `F` is such that `-a ∉ P`,
then the semiring generated by `P` and `a` is still a preordering on `F`.
-/
def RingPreordering.adjoin {a : F} (ha : -a ∉ P) : RingPreordering F where
  __ := Subsemiring.closure (insert a P)
  square_mem' {x} := by
    simpa using Subsemiring.closure_mono
      (by simp : ↑P ⊆ insert a ↑P)
      (Subsemiring.subset_closure <| square_mem P _)
  minus_one_not_mem' := by
    have : ¬ ∃ x ∈ P, ∃ y ∈ P, -1 = x + a * y :=
      by aesop (add (minus_one_not_mem_adjoin_linear P a ha) norm)
    have : -1 ∉ adjoin_linear P a := this
    simpa [Subsemiring.closure_insert_ringPreordering] using this

lemma RingPreordering.subset_adjoin {a : F} (ha : -a ∉ P) : (P : Set F) ⊆ adjoin P ha := by
  simpa using Subsemiring.closure_mono (by simp : ↑P ⊆ insert a ↑P)

lemma RingPreordering.mem_adjoin {a : F} (ha : -a ∉ P) : a ∈ adjoin P ha := by
  simpa using Subsemiring.subset_closure (by simp : a ∈ insert a ↑P)

def RingPreordering.toOrdering (P : RingPreordering F) (h : IsMax P) : RingOrdering F where
  __ := P
  mem_or_neg_mem' {x} := by
    by_contra
    have hx : x ∉ P ∧ -x ∉ P := by aesop
    have : (P : Set F) ⊂ adjoin P hx.2 := by
      rw [Set.ssubset_iff_of_subset (subset_adjoin P hx.2)]
      exact ⟨x, mem_adjoin P hx.2, hx.1⟩
    exact not_isMax_of_lt (by aesop) h

theorem RingPreordering.exists_le_ordering : ∃ O : RingOrdering F, (P : Set F) ⊆ O := by
  suffices ∃ Q, RingPreorderingClass.toRingPreordering P ≤ Q ∧ Maximal (fun x ↦ x ∈ Set.univ) Q by
    obtain ⟨Q, hQl, hQm⟩ := this
    refine ⟨Q.toOrdering (by aesop), by aesop⟩
  apply zorn_le_nonempty₀
  · intro c _ hc P' hP'
    simp_all [← bddAbove_def, RingPreodering.nonempty_chain_bddAbove c hc (Set.nonempty_of_mem hP')]
  · simp

end adjoin_field