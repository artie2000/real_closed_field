/-
Copyright (c) 2024 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.Algebra.Order.Ring.Cone
import Mathlib.Algebra.Ring.Semireal.Defs

/- TODO : decide on definition / sum stuff -/

class IsFormallyReal (R : Type*) [AddCommMonoid R] [Mul R] : Prop where
  eq_zero_of_mul_self_add {a s : R} (hs : IsSumSq s) (h : a * a + s = 0) : a = 0

theorem IsFormallyReal.eq_zero_of_mul_self {R : Type*}
    [AddCommMonoid R] [Mul R] [IsFormallyReal R] {a : R} (h : a * a = 0) : a = 0 :=
  IsFormallyReal.eq_zero_of_mul_self_add IsSumSq.zero (show a * a + 0 = 0 by simpa)

theorem IsFormallyReal.eq_zero_of_add_left {R : Type*}
    [NonUnitalNonAssocSemiring R] [IsFormallyReal R] {s₁ s₂ : R}
    (hs₁ : IsSumSq s₁) (hs₂ : IsSumSq s₂) (h : s₁ + s₂ = 0) : s₁ = 0 := by
  induction hs₁ generalizing s₂
  case zero            => simp_all
  case sq_add a s hs h =>
    have := eq_zero_of_mul_self_add (show IsSumSq (s + s₂) by aesop) (by simpa [← add_assoc])
    aesop

theorem IsFormallyReal.eq_zero_of_add_right {R : Type*}
    [NonUnitalNonAssocSemiring R] [IsFormallyReal R] {s₁ s₂ : R}
    (hs₁ : IsSumSq s₁) (hs₂ : IsSumSq s₂) (h : s₁ + s₂ = 0): s₂ = 0 := by
  simp_all [eq_zero_of_add_left hs₁ hs₂ h]

theorem isFormallyReal_of_eq_zero_of_mul_self_of_eq_zero_of_add
    (R : Type*) [AddCommMonoid R] [Mul R]
    (hz : ∀ {a : R}, a * a = 0 → a = 0)
    (ha : ∀ {S₁ S₂ : R}, IsSumSq S₁ → IsSumSq S₂ → S₁ + S₂ = 0 → S₁ = 0) : IsFormallyReal R where
  eq_zero_of_mul_self_add hs h := hz <| ha (IsSumSq.mul_self _) hs h

instance {R : Type*} [NonAssocSemiring R] [Nontrivial R] [IsFormallyReal R] : IsSemireal R where
  one_add_ne_zero hs h_contr := by
    simpa using IsFormallyReal.eq_zero_of_add_left (by aesop) hs h_contr

instance {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] : IsFormallyReal R where
  eq_zero_of_mul_self_add {a} {s} hs h := mul_self_eq_zero.mp <| le_antisymm
    (by simpa [eq_neg_of_add_eq_zero_left h] using IsSumSq.nonneg hs) (mul_self_nonneg a)

namespace RingCone
variable {T : Type*} [CommRing T] [IsFormallyReal T]

variable (T) in
/--
In a commutative formally real ring `R`, `Subsemiring.sumSq R`
is the cone of sums of squares in `R`.
-/
def sumSq : RingCone T where
  __ := Subsemiring.sumSq T
  eq_zero_of_mem_of_neg_mem' {x} hx hnx :=
    IsFormallyReal.eq_zero_of_add_left (by simpa using hx) (by simpa using hnx) (add_neg_cancel x)

@[simp] lemma sumSq_toSubsemiring : (sumSq T).toSubsemiring = .sumSq T := rfl

@[simp] lemma mem_sumSq {a : T} : a ∈ sumSq T ↔ IsSumSq a :=
  show a ∈ Subsemiring.sumSq T ↔ IsSumSq a by simp

@[simp, norm_cast] lemma coe_sumSq : sumSq T = {x : T | IsSumSq x} :=
  show Subsemiring.sumSq T = {x : T | IsSumSq x} by simp

end RingCone
