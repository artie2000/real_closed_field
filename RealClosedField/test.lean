import Mathlib

def foo (R : Type*) [Ring R] : Subsemiring R → Prop := ⊤

def bar (α : Type*) (P : α → Prop) : Prop := ∀ y : α, False

theorem exists_ge (R : Type*) [CommRing R] (P : Subsemiring R) : ∃ O, P ≤ O := ⟨P, fun _ ↦ id⟩

set_option trace.order true in
theorem result
    {R : Type*} [CommRing R] {O : Subsemiring R} :
    bar _ (foo R) := by
  intro P
  have := exists_ge R P
  rcases this with ⟨Q, hQ⟩
  have : P ≤ Q := by order
  sorry

-- check that order treats defeq types the same
example (a : Fin 3) (b : Fin (2 + 1)) (h : a ≤ b) : LE.le (α := Fin (2 + 1)) a b := by
  order
