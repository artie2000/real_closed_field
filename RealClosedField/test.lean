def p1 : Prop := sorry

def p2 : Prop := sorry

theorem imp : p2 → p1 := sorry

def data (h : p1) := 0

@[simp]
theorem fact (h : p2) : data (imp h) = 0 := rfl

set_option pp.proofs true in
set_option trace.Meta.isDefEq true in
example (h : p2) : data (imp h) = 0 := by simp only [fact]
/-
[Meta.Tactic.simp.discharge] fact discharge ❌️
      p2
[Meta.Tactic.simp.unify] eq_self.{u_1}:1000, failed to unify
      @Eq.{?u.116} ?α ?a ?a
    with
      @Eq.{1} Nat (data (imp h)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
-/
