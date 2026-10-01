/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import RealClosedField.Algebra.Order.Ring.Ordering.Defs
import Mathlib.Tactic.Field
import Mathlib.Tactic.LinearCombination

/-!

We prove basic properties of orderings on rings, and show that they are preserved
under certain operations.

## References

- [*An introduction to real algebra*, T.Y. Lam][lam_1984]

-/

namespace Subsemiring

section CommRing

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
        {P : Subsemiring R} (P' : Subsemiring S)

namespace IsPreordering

theorem of_le (hP : P.IsPreordering) {Q : Subsemiring R} (hPQ : P ≤ Q) (hQ : -1 ∉ Q) :
    Q.IsPreordering where
  mem_of_isSquare := by grind [IsConcreteLE.le_iff, IsPreordering.mem_of_isSquare]

-- TODO : membership tag
theorem unitsInv_mem (hP : P.IsPreordering) {a : Rˣ} (ha : ↑a ∈ P) : ↑a⁻¹ ∈ P := by
  simpa using show (a * (a⁻¹ * a⁻¹) : R) ∈ P by grind [mul_mem, IsPreordering.mul_self_mem]

theorem one_notMem_toAddSubmonoid_support (hP : P.IsPreordering) : 1 ∉ P.support := fun h ↦
  P.neg_one_notMem hP h.2

theorem support_ne_top (hP : P.IsPreordering) : P.support ≠ ⊤ := fun h ↦
  one_notMem_toAddSubmonoid_support hP (by simp [h])

theorem isOrdering_iff (hP : P.IsPreordering) :
    P.IsOrdering ↔ ∀ a b : R, -(a * b) ∈ P → a ∈ P ∨ b ∈ P where
  mp hP a b _ := by
    by_contra
    have : a * b ∈ P := by
      have := Subsemiring.isSpanning_def.mp hP.isSpanning
      grind [mul_mem, mul_neg, neg_mul, neg_neg]
    have : a ∈ P.support ∨ b ∈ P.support :=
      Ideal.IsPrime.mem_or_mem hP.isPrime_supportIdeal (by simp; grind)
    grind [Subsemiring.mem_support]
  mpr h := by
    refine ⟨?_, hP.support_ne_top, fun {x y} ↦ ?_⟩
    · simp [AddSubmonoid.IsSpanning]
      grind [hP.mul_self_mem, neg_mul, mul_neg, neg_neg] -- TODO : figure out why `grind` doesn't know `neg_neg`
    · simp_rw [Subsemiring.mem_support]
      by_contra
      have := h (-x) y
      have := h (-x) (-y)
      have := h x y
      have := h x (-y)
      cases (by simp_all : x ∈ P ∨ -x ∈ P) <;> simp_all

theorem smul_mem_support_of_isUnit_two (h : IsUnit (2 : R))
    (x : R) {a : R} (ha : a ∈ P.support) : x * a ∈ P.support := by
  rcases h.exists_right_inv with ⟨half, h2⟩
  set y := (1 + x) * half
  set z := (1 - x) * half
  rw [show x = y ^ 2 - z ^ 2 by
    linear_combination (- x - x * half * 2) * h2]
  ring_nf
  aesop (add simp sub_eq_add_neg)

end IsPreordering

theorem IsPreordering.of_isSpanning_of_isPointed [Nontrivial R]
    (hP₁ : P.IsSpanning) (hP₂ : P.IsPointed) : P.IsPreordering :=
  .of_ne_top hP₁ fun hc ↦ one_ne_zero' R (by simp_all [AddSubmonoid.IsPointed]) -- TODO : ¬ T.IsPointed

theorem IsOrdering.of_isSpanning_of_isPointed [IsDomain R]
    (hP₁ : P.IsSpanning) (hP₂ : P.IsPointed) : P.IsOrdering where
  isSpanning := hP₁
  support_ne_top := by simp [hP₂]
  mem_support_or_mem_support := by simp [hP₂]

theorem IsPreordering.of_isPointed [Nontrivial R]
    (hP : P.IsPointed) (h : .sumSq R ≤ P) : P.IsPreordering where
  mem_of_isSquare hx := h (by simpa using hx.isSumSq)
  neg_one_notMem := by
    rw [Subsemiring.isPointed_def] at hP
    grind [one_mem, one_ne_zero]

-- PR SPLIT ↑1 ↓2

-- TODO : upstream and add similar
attribute [simp] Submonoid.mem_sInf
attribute [simp] AddSubmonoid.mem_sInf
attribute [simp] Subsemiring.mem_sInf

theorem IsPreordering.inf {P₁ P₂ : Subsemiring R} (hP₁ : P₁.IsPreordering) (hP₂ : P₂.IsPreordering) :
    (P₁ ⊓ P₂).IsPreordering where
  mem_of_isSquare := by grind [mem_inf, mem_of_isSquare]
  neg_one_notMem := by grind [mem_inf, neg_one_notMem]

theorem IsPreordering.sInf {S : Set (Subsemiring R)}
    (hSn : S.Nonempty) (hS : ∀ s ∈ S, s.IsPreordering) : (sInf S).IsPreordering where
  neg_one_notMem := by
    have := hS _ hSn.some_mem
    simpa using ⟨_, hSn.some_mem, hSn.some.neg_one_notMem⟩

theorem IsPreordering.sSup  {S : Set (Subsemiring R)}
    (hSn : S.Nonempty) (hSd : DirectedOn (· ≤ ·) S)
    (hS : ∀ s ∈ S, s.IsPreordering) : (sSup S).IsPreordering where
  mem_of_isSquare x := by
    have := Set.Nonempty.some_mem hSn
    simpa [mem_sSup_of_directedOn hSn hSd] using ⟨_, this, by aesop⟩
  neg_one_notMem := by
    simpa [mem_sSup_of_directedOn hSn hSd] using (fun x hx ↦ have := hS _ hx; neg_one_notMem x)

theorem IsOrdering.comap (hP' : P'.IsOrdering) : IsOrdering (P'.comap f) := .mk'
  (isSpanning_comap f (IsOrdering.isSpanning P'))
  (by simpa using inferInstanceAs (Ideal.comap f P'.support).IsPrime)

theorem IsPreordering.comap (hP' : P'.IsPreordering) : (P'.comap f).IsPreordering where
  mem_of_isSquare := by grind [mem_comap, mem_of_isSquare]
  neg_one_notMem := by grind [mem_comap, neg_one_notMem]

variable {f P} in
theorem IsOrdering.map (hP : P.IsOrdering) (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f).toAddSubgroup ≤ P.support) : IsOrdering (P.map f) := mk'
  (isSpanning_map (IsOrdering.isSpanning P) hf) <| by
    simpa [*] using Ideal.map_isPrime_of_surjective hf hsupp

variable {f} in
theorem IsPreordering.map (hP : P.IsPreordering) (hf : Function.Surjective f)
    (hsupp : f.toAddMonoidHom.ker ≤ P.toAddSubmonoid.support) : (P.map f).IsPreordering where
  mem_of_isSquare hx := by
    rcases isSquare_subset_image_isSquare hf hx with ⟨x, hx, hfx⟩
    exact ⟨x, by aesop⟩
  neg_one_notMem := fun ⟨x', hx', _⟩ ↦ by
    have : -(x' + 1) + x' ∈ P := add_mem (hsupp (show f (x' + 1) = 0 by simp_all)).2 hx'
    aesop

end CommRing

-- PR SPLIT ↑2 ↓1

section Field

variable {F : Type*} [Field F] {P : Subsemiring F}

namespace IsPreordering

-- TODO : membership
theorem inv_mem (hP : IsPreordering P) {a : F} (ha : a ∈ P) : a⁻¹ ∈ P := by
  suffices a * (a⁻¹ * a⁻¹) ∈ P by convert this; field
  grind [mul_mem, IsPreordering.mul_self_mem]

theorem isPointed (hP : IsPreordering P) : P.IsPointed := by
  rw [Subsemiring.isPointed_def]
  grind [P.neg_one_notMem hP, neg_mul_mem, inv_mem]

end IsPreordering

end Field

end Subsemiring
