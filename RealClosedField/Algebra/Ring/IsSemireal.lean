import RealClosedField.Algebra.Order.Ring.Ordering.Defs
import RealClosedField.Upstream
import Mathlib.Algebra.Ring.IsSemireal.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Ring.IsSemireal

variable (R : Type*)

instance [NonAssocSemiring R] [Nontrivial R] [IsFormallyReal R] : IsSemireal R where
  one_add_ne_zero hs h_contr := by
    simpa using IsFormallyReal.eq_zero_of_add_right IsSumSq.one hs h_contr

/--
Linearly ordered semirings with the property `a ≤ b → ∃ c, a + c = b` (e.g. `ℕ`)
are semireal.
-/
instance [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R] : IsSemireal R where
  one_add_ne_zero hs amo := zero_ne_one' R (le_antisymm zero_le_one
                              (le_of_le_of_eq (le_add_of_nonneg_right hs.nonneg) amo))

instance [NonAssocRing R] [IsSemireal R] : CharZero R :=
  charZero_of_inj_zero fun n hn ↦ by
    cases n with
    | zero => rfl
    | succ n =>
        rw [add_comm] at hn
        push_cast at hn
        simpa using IsSemireal.one_add_ne_zero (by simp) hn

section CommRing

variable [CommRing R]

instance [IsSemireal R] : (Subsemiring.sumSq R).IsPreordering where
  neg_one_notMem := by simpa using IsSemireal.not_isSumSq_neg_one R

variable {R} in
theorem isSemireal_ofIsPreordering (P : Subsemiring R) [P.IsPreordering] : IsSemireal R :=
  .of_not_isSumSq_neg_one (P.neg_one_notMem <| P.mem_of_isSumSq ·)

variable {R} in
theorem exists_isPreordering_iff_isSemireal :
    (∃ P : Subsemiring R, P.IsPreordering) ↔ IsSemireal R where
  mp | ⟨P, _⟩ => isSemireal_ofIsPreordering P
  mpr _ := ⟨Subsemiring.sumSq R, inferInstance⟩

end CommRing

instance {F : Type*} [Field F] [IsSemireal F] : IsFormallyReal F :=
  .of_eq_zero_of_eq_zero_of_mul_self_add F <| fun {s} {a} _ h ↦ by
    by_contra
    exact IsSemireal.one_add_ne_zero (s := s * a⁻¹ ^ 2) (by aesop)
      (by field_simp; linear_combination h)
