import Mathlib.Algebra.Ring.Regular
import Mathlib.RingTheory.Localization.FractionRing

/- TODO: ordering on an ID <-> ordering on its fraction field -/

open Localization nonZeroDivisors in
theorem extracted {R : Type*} [LinearOrderedCommRing R] {s : Submonoid R} (hs : 0 ∉ s)
    {a₁ b₁ : R} {a₂ b₂ : ↥s} {c₁ d₁ : R} {c₂ d₂ : ↥s} (hab : (r s) (a₁, a₂) (b₁, b₂))
    (hcd : (r s) (c₁, c₂) (d₁, d₂)) :
    (fun a₁ a₂ b₁ b₂ ↦ ↑a₂ * (b₂ : R) * ↑b₂ * a₁ ≤ ↑b₂ * ↑a₂ * ↑a₂ * b₁) a₁ a₂ c₁ c₂ ↔
    (fun a₁ a₂ b₁ b₂ ↦ ↑a₂ * (b₂ : R) * ↑b₂ * a₁ ≤ ↑b₂ * ↑a₂ * ↑a₂ * b₁) b₁ b₂ d₁ d₂ := by
  rw [r_iff_exists] at *
  rcases hab, hcd with ⟨⟨e, he⟩, ⟨f, hf⟩⟩
  have : ∀ x, x ∈ s → x ≠ 0 := by aesop
  simp_all only [mul_eq_mul_left_iff, SetLike.coe_mem, or_false, ne_eq]
  rw [← mul_le_mul_left (show (b₂ : R) * ↑b₂ > 0 by aesop)]
  rw [show ↑b₂ * ↑b₂ * (↑a₂ * ↑c₂ * ↑c₂ * a₁) = ↑b₂ * a₁ * (↑a₂ * ↑c₂ * ↑c₂ * ↑b₂) by ring]
  rw [he]
  rw [show ↑a₂ * b₁ * (↑a₂ * ↑c₂ * ↑c₂ * ↑b₂) = ↑a₂ * ↑a₂ * (↑c₂ * ↑c₂ * ↑b₂ * b₁) by ring]
  rw [show ↑b₂ * ↑b₂ * (↑c₂ * ↑a₂ * ↑a₂ * c₁) = ↑a₂ * ↑a₂ * (↑c₂ * ↑b₂ * ↑b₂ * c₁) by ring]
  rw [mul_le_mul_left (show (a₂ : R) * ↑a₂ > 0 by aesop)]
  rw [← mul_le_mul_left (show (d₂ : R) * ↑d₂ > 0 by aesop)]
  rw [show ↑d₂ * ↑d₂ * (↑c₂ * ↑b₂ * ↑b₂ * c₁) = ↑d₂ * c₁ * (↑c₂ * ↑b₂ * ↑b₂ * ↑d₂) by ring]
  rw [hf]
  rw [show ↑c₂ * d₁ * (↑c₂ * ↑b₂ * ↑b₂ * ↑d₂) = ↑c₂ * ↑c₂ * (↑d₁ * ↑b₂ * ↑b₂ * ↑d₂) by ring]
  rw [show ↑d₂ * ↑d₂ * (↑c₂ * ↑c₂ * ↑b₂ * b₁) = ↑c₂ * ↑c₂ * (↑d₂ * ↑d₂ * ↑b₂ * b₁) by ring]
  rw [mul_le_mul_left (show (c₂ : R) * ↑c₂ > 0 by aesop)]
  ring_nf

open Localization nonZeroDivisors in
instance {R : Type*} [LinearOrderedCommSemiring R] {s : Submonoid R} (hs : 0 ∉ s) :
    LE (Localization s) where
  le a b := Localization.liftOn₂ a b (fun a₁ a₂ b₁ b₂ => a₂ * b₂ * b₂ * a₁ ≤ b₂ * a₂ * a₂ * b₁)
    fun {a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂} hab hcd => propext <| by
      have : ∀ x, x ∈ s → x ≠ 0 := by aesop
      rw [r_iff_exists] at *
      rcases hab, hcd with ⟨⟨e, he⟩, ⟨f, hf⟩⟩
      simp_all only [mul_eq_mul_left_iff, SetLike.coe_mem, or_false, ne_eq]
      rw [← mul_le_mul_left (show (b₂ : R) * ↑b₂ > 0 by aesop)]
      rw [show ↑b₂ * ↑b₂ * (↑a₂ * ↑c₂ * ↑c₂ * a₁) = ↑b₂ * a₁ * (↑a₂ * ↑c₂ * ↑c₂ * ↑b₂) by ring]
      rw [he]
      rw [show ↑a₂ * b₁ * (↑a₂ * ↑c₂ * ↑c₂ * ↑b₂) = ↑a₂ * ↑a₂ * (↑c₂ * ↑c₂ * ↑b₂ * b₁) by ring]
      rw [show ↑b₂ * ↑b₂ * (↑c₂ * ↑a₂ * ↑a₂ * c₁) = ↑a₂ * ↑a₂ * (↑c₂ * ↑b₂ * ↑b₂ * c₁) by ring]
      rw [mul_le_mul_left (show (a₂ : R) * ↑a₂ > 0 by aesop)]
      rw [← mul_le_mul_left (show (d₂ : R) * ↑d₂ > 0 by aesop)]
      rw [show ↑d₂ * ↑d₂ * (↑c₂ * ↑b₂ * ↑b₂ * c₁) = ↑d₂ * c₁ * (↑c₂ * ↑b₂ * ↑b₂ * ↑d₂) by ring]
      rw [hf]
      rw [show ↑c₂ * d₁ * (↑c₂ * ↑b₂ * ↑b₂ * ↑d₂) = ↑c₂ * ↑c₂ * (↑d₁ * ↑b₂ * ↑b₂ * ↑d₂) by ring]
      rw [show ↑d₂ * ↑d₂ * (↑c₂ * ↑c₂ * ↑b₂ * b₁) = ↑c₂ * ↑c₂ * (↑d₂ * ↑d₂ * ↑b₂ * b₁) by ring]
      rw [mul_le_mul_left (show (c₂ : R) * ↑c₂ > 0 by aesop)]
      ring_nf

instance {R : Type} [LinearOrderedCommRing R] [NoZeroDivisors R] :
    LinearOrderedField (FractionRing R) where
  __ := (inferInstance : Field (FractionRing R))
  __ := (inferInstance : CancelCommMonoidWithZero R)
  __ := (inferInstance : LinearOrderedCommGroupWithZero (FractionRing R))

#min_imports
