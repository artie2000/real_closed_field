/-
Copyright (c) 2024 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.Algebra.Ring.Subsemiring.Support
import Mathlib.Algebra.Ring.SumsOfSquares

-- TODO : upstream
theorem AddSubmonoid.closure_eq_image_multiset_sum {M : Type*} [AddCommMonoid M] (s : Set M) :
    ↑(closure s) = Multiset.sum '' {m : Multiset M | ∀ x ∈ m, x ∈ s} := by
  ext x
  refine ⟨fun h ↦ AddSubmonoid.exists_multiset_of_mem_closure h, fun h ↦ ?_⟩
  rcases h with ⟨m, hm, rfl⟩
  exact AddSubmonoid.multiset_sum_mem _ _ (by aesop)

-- TODO : upstream
theorem isSumSq_iff_exists_sum_mul_self_eq {R : Type*} [AddCommMonoid R] [Mul R] {x} :
    IsSumSq x ↔ ∃ s : Multiset R, (s.map (fun a ↦ a * a)).sum = x := by
  rw [← AddSubmonoid.mem_sumSq, ← AddSubmonoid.closure_isSquare, ← SetLike.mem_coe,
      AddSubmonoid.closure_eq_image_multiset_sum, Set.mem_image]
  refine ⟨fun h => ?_, fun ⟨m, hm⟩ => ⟨Multiset.map (fun a ↦ a * a) m, by simp [hm]⟩⟩
  rcases h with ⟨m, hm, rfl⟩
  choose! sqrt hsqrt using hm
  exact ⟨m.map sqrt, by simp [← Multiset.map_congr _ hsqrt]⟩

variable (R : Type*)

class IsFormallyReal [AddCommMonoid R] [Mul R] : Prop where
  eq_zero_of_sum_eq_zero : ∀ {s : Multiset R}, (s.map (fun a ↦ a * a)).sum = 0 → ∀ a ∈ s, a = 0

namespace IsFormallyReal

theorem of_eq_zero_of_mul_self_of_eq_zero_of_add [AddCommMonoid R] [Mul R]
    (hz : ∀ {a : R}, a * a = 0 → a = 0)
    (ha : ∀ {s₁ s₂ : R}, IsSumSq s₁ → IsSumSq s₂ → s₁ + s₂ = 0 → s₁ = 0) : IsFormallyReal R where
  eq_zero_of_sum_eq_zero {s} := by
    induction s using Multiset.induction with
    | empty => simp
    | cons a m hm =>
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.mem_cons, forall_eq_or_imp]
        intro h
        have := ha (by simp) (by rw [isSumSq_iff_exists_sum_mul_self_eq]; simp) h
        exact ⟨hz this, hm (by simpa [this] using h)⟩

theorem of_eq_zero_of_eq_zero_of_mul_self_add [NonUnitalNonAssocSemiring R]
    (h : ∀ {s a : R}, IsSumSq s → a * a + s = 0 → a = 0) : IsFormallyReal R where
  eq_zero_of_sum_eq_zero {s} := by
    induction s using Multiset.induction with
    | empty => simp
    | cons a m hm =>
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.mem_cons, forall_eq_or_imp]
        intro has
        have := h (by rw [isSumSq_iff_exists_sum_mul_self_eq]; simp) has
        exact ⟨this, hm (by simpa [this] using has)⟩

instance [Ring R] [LinearOrder R] [IsStrictOrderedRing R] : IsFormallyReal R :=
  of_eq_zero_of_mul_self_of_eq_zero_of_add R mul_self_eq_zero.mp <|
    fun hs₁ hs₂ h ↦ ((add_eq_zero_iff_of_nonneg (IsSumSq.nonneg hs₁) (IsSumSq.nonneg hs₂)).mp h).1

variable {R}

theorem eq_zero_of_mul_self [AddCommMonoid R] [Mul R] [IsFormallyReal R] {a : R} :
  a * a = 0 → a = 0 := by simpa using IsFormallyReal.eq_zero_of_sum_eq_zero (s := {a})

theorem eq_zero_of_add_right [NonUnitalNonAssocSemiring R] [IsFormallyReal R]
    {s₁ s₂ : R} (hs₁ : IsSumSq s₁) (hs₂ : IsSumSq s₂) (h : s₁ + s₂ = 0) : s₁ = 0 := by
  simp_rw [isSumSq_iff_exists_sum_mul_self_eq] at *
  rcases hs₁ with ⟨m₁, rfl⟩
  rcases hs₂ with ⟨m₂, rfl⟩
  rw [← Multiset.sum_add, ← Multiset.map_add] at h
  exact Multiset.sum_eq_zero <|by
    simpa using fun _ _ ↦ by simp [eq_zero_of_sum_eq_zero h _ (by aesop)]

theorem eq_zero_of_add_left [NonUnitalNonAssocSemiring R] [IsFormallyReal R]
    {s₁ s₂ : R} (hs₁ : IsSumSq s₁) (hs₂ : IsSumSq s₂) (h : s₁ + s₂ = 0): s₂ = 0 := by
  simp_all [eq_zero_of_add_right hs₁ hs₂ h]

theorem eq_zero_of_isSumSq_of_neg_isSumSq [NonUnitalNonAssocRing R] [IsFormallyReal R]
    {s : R} (h₁ : IsSumSq s) (h₂ : IsSumSq (-s)) : s = 0 :=
  IsFormallyReal.eq_zero_of_add_right h₁ h₂ (by simp)

instance [CommRing R] [IsFormallyReal R] : (AddSubmonoid.sumSq R).IsPointed where
  eq_zero_of_mem_of_neg_mem {_} := by simpa using eq_zero_of_isSumSq_of_neg_isSumSq

-- TODO : upstream to `Mathlib.Algebra.Ring.SumsOfSquares`
@[simp]
theorem Subsemiring.sumSq_toAddSubmonoid {T : Type*} [CommSemiring T] :
    (Subsemiring.sumSq T).toAddSubmonoid = .sumSq T :=
  show (Subsemiring.sumSq T).toNonUnitalSubsemiring.toAddSubmonoid = .sumSq T by simp

instance [CommRing R] [IsFormallyReal R] : (Subsemiring.sumSq R).IsPointed := by
  simpa using (inferInstance : (AddSubmonoid.sumSq R).IsPointed)

end IsFormallyReal
