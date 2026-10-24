import Mathlib.Algebra.Ring.Regular
import Mathlib.RingTheory.Localization.FractionRing

/- TODO : ordering on an ID <-> ordering on its fraction field -/
/- TODO : more generally, orderings on a localization at `s` correspond to
          orderings with support disjoint from `s` -/

-- TODO : switch to ring cone method

-- ⚠ some of the statements and proofs are AI-generated and have not yet been deslopified

theorem nontrivial_localization_iff_le_nonZeroDivisors
    {R : Type*} [CommRing R] [IsDomain R] {s : Submonoid R} :
    Nontrivial (Localization s) ↔ s ≤ nonZeroDivisors R := by
  grind [OreLocalization.nontrivial_iff, IsConcreteLE.le_iff, mem_nonZeroDivisors_iff_ne_zero]

theorem le_nonZeroDivisors_of_nontrivial_localization
    {R : Type*} [CommRing R] [IsDomain R]
    (s : Submonoid R) [i : Nontrivial (Localization s)] :
    s ≤ nonZeroDivisors R := nontrivial_localization_iff_le_nonZeroDivisors.mp i

namespace Localization

theorem coe_denom_ne_zero {R : Type*} [CommRing R] {s : Submonoid R} [Nontrivial (Localization s)]
    (a : s) : (a : R) ≠ 0 := by grind [OreLocalization.nontrivial_iff]

theorem r_iff_of_nontrivial {R : Type*} [CommRing R] [IsDomain R] {s : Submonoid R}
    [Nontrivial (Localization s)] (a c : R) (b d : s) : (r s) (a, b) (c, d) ↔ a * d = b * c :=
  r_iff_of_le_nonZeroDivisors (le_nonZeroDivisors_of_nontrivial_localization _) ..

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (s : Submonoid R)
  [Nontrivial (Localization s)]

instance le₀ : LE (Localization s) where
  le a b := liftOn₂ a b (fun a₁ a₂ b₁ b₂ ↦ a₂ * b₂ * b₂ * a₁ ≤ b₂ * a₂ * a₂ * b₁)
    fun {a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂} hab hcd ↦ propext <| by
      rw [r_iff_of_nontrivial] at hab hcd
      have hsq_pos (x : s) : 0 < (x : R) * x := by
        grind [mul_self_pos, coe_denom_ne_zero]
      rw [← mul_le_mul_iff_right₀ (hsq_pos b₂)]
      suffices (a₁ : R) * b₂ * (a₂ * c₂ * c₂ * b₂) ≤ b₂ * b₂ * (c₂ * a₂ * a₂ * c₁) ↔
          b₂ * d₂ * d₂ * b₁ ≤ d₂ * b₂ * b₂ * d₁ by grind
      rw [hab]
      suffices (a₂ : R) * a₂ * (c₂ * c₂ * b₂ * b₁) ≤ a₂ * a₂ * (c₂ * b₂ * b₂ * c₁) ↔
          b₂ * d₂ * d₂ * b₁ ≤ d₂ * b₂ * b₂ * d₁ by grind
      rw [mul_le_mul_iff_right₀ (hsq_pos a₂)]
      rw [← mul_le_mul_iff_right₀ (hsq_pos d₂)]
      suffices (d₂ : R) * d₂ * (c₂ * c₂ * b₂ * b₁) ≤ c₁ * d₂ * (c₂ * b₂ * b₂ * d₂) ↔
          b₂ * d₂ * d₂ * b₁ ≤ d₂ * b₂ * b₂ * d₁ by grind
      rw [hcd]
      suffices (c₂ : R) * c₂ * (d₂ * d₂ * b₂ * b₁) ≤ c₂ * c₂ * (d₁ * b₂ * b₂ * d₂) ↔
          b₂ * d₂ * d₂ * b₁ ≤ d₂ * b₂ * b₂ * d₁ by grind
      rw [mul_le_mul_iff_right₀ (hsq_pos c₂)]
      ring_nf

variable {s} in
@[simp]
theorem mk_le_mk₀ {a₁ b₁ : R} {a₂ b₂ : s} :
    mk a₁ a₂ ≤ mk b₁ b₂ ↔ a₂ * b₂ * b₂ * a₁ ≤ b₂ * a₂ * a₂ * b₁ := .rfl

instance partialOrder₀ : PartialOrder (Localization s) where
  __ := le₀ s
  le_refl a := a.induction_on (by simp)
  le_trans a b c := induction_on₃ a b c fun a b c hab hbc => by
      simp only [mk_le_mk₀] at hab hbc ⊢
      rw [← mul_le_mul_iff_right₀
        (show 0 < (b.2 : R) * b.2 by grind [mul_self_pos, coe_denom_ne_zero])]
      calc
        ((b.2 : R) * b.2) * (a.2 * c.2 * c.2 * a.1)
            = ((c.2 : R) * c.2) * (a.2 * b.2 * b.2 * a.1) := by ring
        _ ≤ ((c.2 : R) * c.2) * (b.2 * a.2 * a.2 * b.1) := by
          exact mul_le_mul_of_nonneg_left hab (by simpa [sq] using sq_nonneg (c.2 : R))
        _ = ((a.2 : R) * a.2) * (b.2 * c.2 * c.2 * b.1) := by ring
        _ ≤ ((a.2 : R) * a.2) * (c.2 * b.2 * b.2 * c.1) := by
          exact mul_le_mul_of_nonneg_left hbc (by simpa [sq] using sq_nonneg (a.2 : R))
        _ = ((b.2 : R) * b.2) * (c.2 * a.2 * a.2 * c.1) := by ring
  le_antisymm a b := induction_on₂ a b fun a b hab hba => by
      simp only [mk_le_mk₀] at hab hba
      rw [mk_eq_mk_iff, r_iff_of_nontrivial]
      apply mul_left_cancel₀
        (mul_ne_zero (coe_denom_ne_zero a.2) (coe_denom_ne_zero b.2))
      grind [hab.antisymm hba]

instance linearOrder₀ : LinearOrder (Localization s) where
  __ := partialOrder₀ s
  le_total a b := induction_on₂ a b fun a b => by simpa using le_total ..
  toDecidableLE a b := recOnSubsingleton₂ a b fun _ _ _ _ => decidable_of_iff' _ mk_le_mk₀

instance zeroLEOne₀ : ZeroLEOneClass (Localization s) where
  zero_le_one := by simp [← mk_zero 1, ← mk_one, mk_le_mk₀]

instance isOrderedAddMonoid₀ : IsOrderedAddMonoid (Localization s) where
  add_le_add_left a b hab c := by
    induction a, b, c using induction_on₃ with
    | H a b c =>
      simp_rw [add_mk, mk_le_mk₀] at hab ⊢
      calc
        ((a.2 : R) * c.2) * (b.2 * c.2) * (b.2 * c.2) *
            (a.2 * c.1 + c.2 * a.1)
            = a.2 * a.2 * b.2 * b.2 * c.2 * c.2 * c.2 * c.1 +
              (a.2 * b.2 * b.2 * a.1) * (((c.2 : R) * c.2) * (c.2 * c.2)) := by ring
        _ ≤ a.2 * a.2 * b.2 * b.2 * c.2 * c.2 * c.2 * c.1 +
              (b.2 * a.2 * a.2 * b.1) * (((c.2 : R) * c.2) * (c.2 * c.2)) :=
          add_le_add_right (mul_le_mul_of_nonneg_right hab
            (mul_nonneg (mul_self_nonneg _) (mul_self_nonneg _))) _
        _ = ((b.2 : R) * c.2) * (a.2 * c.2) * (a.2 * c.2) *
            (b.2 * c.1 + c.2 * b.1) := by ring

instance isOrderedRing₀ : IsOrderedRing (Localization s) :=
  .of_mul_nonneg fun a b => induction_on₂ a b fun _ _ ha hb => by
      simp_all [← mk_zero 1, mk_mul]
      grind [mul_nonneg ha hb]

#synth IsStrictOrderedRing (FractionRing R)

end Localization
