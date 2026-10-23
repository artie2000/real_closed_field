import Mathlib.Algebra.Ring.Regular
import Mathlib.RingTheory.Localization.FractionRing

/- TODO : ordering on an ID <-> ordering on its fraction field -/
/- TODO : more generally, orderings on a localization at `s` correspond to
          orderings with support disjoint from `s` -/

namespace Localization

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (s : Submonoid R)
  [Nontrivial (Localization s)]

instance le₀ : LE (Localization s) where
  le a b := Localization.liftOn₂ a b (fun a₁ a₂ b₁ b₂ ↦ a₂ * b₂ * b₂ * a₁ ≤ b₂ * a₂ * a₂ * b₁)
    fun {a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂} hab hcd ↦ propext <| by
      rcases a₂, b₂, c₂, d₂ with
        ⟨⟨a₂, ha₂⟩, ⟨b₂, hb₂⟩, ⟨c₂, hc₂⟩, ⟨d₂, hd₂⟩⟩
      rcases r_iff_exists.mp hab, r_iff_exists.mp hcd with ⟨⟨_, he⟩, ⟨_, hf⟩⟩
      have hpos : ∀ x, x ∈ s → x ≠ 0 := by grind [OreLocalization.nontrivial_iff]
      simp_all only [mul_eq_mul_left_iff, SetLike.coe_mem, or_false, ne_eq]
      rw [← mul_le_mul_iff_right₀ (show 0 < b₂ * b₂ by simp [*])]
      suffices b₂ * a₁ * (a₂ * c₂ * c₂ * b₂) ≤
        b₂ * b₂ * (c₂ * a₂ * a₂ * c₁) ↔ b₂ * d₂ * d₂ * b₁ ≤ d₂ * b₂ * b₂ * d₁ by grind
      rw [he]
      suffices a₂ * a₂ * (c₂ * c₂ * b₂ * b₁) ≤
        a₂ * a₂ * (c₂ * b₂ * b₂ * c₁) ↔ b₂ * d₂ * d₂ * b₁ ≤ d₂ * b₂ * b₂ * d₁ by grind
      rw [mul_le_mul_iff_right₀ (show 0 < a₂ * a₂ by simp [*])]
      rw [← mul_le_mul_iff_right₀ (show 0 < d₂ * d₂ by simp [*])]
      suffices d₂ * d₂ * (c₂ * c₂ * b₂ * b₁) ≤
        d₂ * c₁ * (c₂ * b₂ * b₂ * d₂) ↔ b₂ * d₂ * d₂ * b₁ ≤ d₂ * b₂ * b₂ * d₁ by grind
      rw [hf]
      suffices c₂ * c₂ * (d₂ * d₂ * b₂ * b₁) ≤
        c₂ * c₂ * (d₁ * b₂ * b₂ * d₂) ↔ b₂ * d₂ * d₂ * b₁ ≤ d₂ * b₂ * b₂ * d₁ by grind
      rw [mul_le_mul_iff_right₀ (show 0 < c₂ * c₂ by simp [*])]
      ring_nf

variable {s} in
@[simp]
theorem mk_le_mk₀ {a₁ b₁ : R} {a₂ b₂ : s} :
    let := le₀ s
    mk a₁ a₂ ≤ mk b₁ b₂ ↔ a₂ * b₂ * b₂ * a₁ ≤ b₂ * a₂ * a₂ * b₁ := .rfl

instance partialOrder₀ : PartialOrder (Localization s) where
  __ := le₀ s
  le_refl a := a.induction_on (by simp)
  le_trans a b c :=
    Localization.induction_on₃ a b c fun a b c hab hbc => by
      simp_all

      simp only [mk_le_mk] at hab hbc ⊢
      apply le_of_mul_le_mul_left' _
      · exact ↑b.2
      grw [mul_left_comm, hab]
      rwa [mul_left_comm, mul_left_comm (b.2 : α), mul_le_mul_iff_left]
  le_antisymm a b := by
    induction a using Localization.rec
    on_goal 1 =>
      induction b using Localization.rec
      · simp_rw [mk_le_mk₀, mk_eq_mk_iff, r_iff_exists]
        exact fun hab hba => ⟨1, by rw [hab.antisymm hba]⟩
    all_goals rfl

instance linearOrder₀ : LinearOrder (Localization s) where
  __ := partialOrder₀ s
  le_total := by sorry
  toDecidableLE := by sorry

#synth LinearOrder (FractionRing R)
#synth CommRing (FractionRing R)
#synth IsStrictOrderedRing (FractionRing R)

end Localization
