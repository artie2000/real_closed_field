/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Henselian
import RealClosedField.OrderedAlgebra

/- An ordered field is real closed if every nonegative element is a square and
   every odd-degree polynomial has a root. -/
class IsRealClosed (R : Type*) [Field R] [LinearOrder R] [IsOrderedRing R] : Prop where
  isSquare_of_nonneg' {x : R} (hx : x ≥ 0) : IsSquare x
  exists_isRoot_of_odd_natDegree' {f : Polynomial R} (hf : Odd f.natDegree) : ∃ x, f.IsRoot x

/- A real closure is a real closed ordered algebraic extension. -/
class IsRealClosure (K R : Type*) [Field K] [Field R] [LinearOrder K] [LinearOrder R]
    [IsOrderedRing K] [IsOrderedRing R] [OrderedAlgebra K R] where
  isRealClosed : IsRealClosed K
  isAlgebraic : Algebra.IsAlgebraic K R

open Polynomial
variable {F : Type*} [Field F] [LinearOrder F] [IsOrderedRing F] (f : F[X])

/- needed for linarith to work -/
/- TODO : upstream global instance -/
instance {F : Type*} [Field F] [LinearOrder F] [IsOrderedRing F] : IsStrictOrderedRing F :=
  IsOrderedRing.toIsStrictOrderedRing F

open Finset in
variable {f} in
theorem estimate (hdeg : f.natDegree ≠ 0) {x : F} (hx : 1 ≤ x) :
    x ^ (f.natDegree - 1) * (f.leadingCoeff * x -
      f.natDegree * (image (|f.coeff ·|) (range f.natDegree)).max'
        (by simpa using hdeg)) ≤ f.eval x := by
  generalize_proofs ne
  set M := (image (|f.coeff ·|) (range f.natDegree)).max' ne
  have hM : ∀ i < f.natDegree, |f.coeff i| ≤ M := fun i hi ↦
    le_max' _ _ <| mem_image_of_mem (|f.coeff ·|) (by simpa using hi)
  have hM₀ : 0 ≤ M := (abs_nonneg _).trans (hM 0 (by omega))
  rw [Polynomial.eval_eq_sum_range, sum_range_succ, ← leadingCoeff]
  suffices f.natDegree * (-M * x ^ (f.natDegree - 1)) ≤
           ∑ i ∈ range f.natDegree, f.coeff i * x ^ i by
    have hxpow : x * x ^ (f.natDegree - 1) = x ^ f.natDegree := by
      rw [← pow_succ', show f.natDegree - 1 + 1 = f.natDegree by omega]
    linear_combination this + hxpow * f.leadingCoeff
  suffices ∀ i < f.natDegree, -M * x ^ (f.natDegree - 1) ≤ f.coeff i * x ^ i by
    simpa using card_nsmul_le_sum (range f.natDegree) (fun i ↦ f.coeff i * x ^ i)
      (-M * x ^ (f.natDegree - 1)) (by simpa using this)
  intro i hi
  calc
    -M * x ^ (f.natDegree - 1) ≤ -M * x ^ i :=
      mul_le_mul_of_nonpos_left (by gcongr; exacts [hx, by omega]) (by simpa using hM₀)
    _ ≤ f.coeff i * x ^ i := by gcongr; exact neg_le_of_abs_le (hM _ hi)

variable {f} in
theorem eventually_pos (hdeg : f.natDegree ≠ 0) (hf : 0 < f.leadingCoeff) :
    ∃ y : F, ∀ x, y < x → 0 < f.eval x := by
  set z := (Finset.image (|f.coeff ·|) (Finset.range f.natDegree)).max' (by simpa using hdeg)
  use max 1 (f.natDegree * z / f.leadingCoeff)
  intro x hx
  have one_lt_x : 1 < x := lt_of_le_of_lt (le_max_left ..) hx
  have := calc
    f.eval x ≥ x ^ (f.natDegree - 1) * (f.leadingCoeff * x - f.natDegree * z) :=
      estimate hdeg (le_of_lt one_lt_x)
    _ > x ^ (f.natDegree - 1) * (f.leadingCoeff * (max 1 (f.natDegree * z / f.leadingCoeff)) -
        f.natDegree * z) := by gcongr
    _ ≥ x ^ (f.natDegree - 1) * (f.leadingCoeff * (f.natDegree * z / f.leadingCoeff) -
        f.natDegree * z) := by gcongr; exact le_max_right ..
  field_simp at this
  assumption

open Finset in
variable {f} in
theorem estimate2 (hdeg : Odd f.natDegree) {x : F} (hx : x ≤ -1) :
    f.eval x ≤ x ^ (f.natDegree - 1) * (f.leadingCoeff * x +
      f.natDegree * (image (|f.coeff ·|) (range f.natDegree)).max'
        (by simpa using Nat.ne_of_odd_add hdeg)) := by
  generalize_proofs ne
  have : f.natDegree ≠ 0 := Nat.ne_of_odd_add hdeg
  set M := (image (|f.coeff ·|) (range f.natDegree)).max' ne
  have hM : ∀ i < f.natDegree, |f.coeff i| ≤ M := fun i hi ↦
    le_max' _ _ <| mem_image_of_mem (|f.coeff ·|) (by simpa using hi)
  have hM₀ : 0 ≤ M := (abs_nonneg _).trans (hM 0 (by omega))
  rw [Polynomial.eval_eq_sum_range, sum_range_succ, ← leadingCoeff]
  suffices ∑ i ∈ range f.natDegree, f.coeff i * x ^ i ≤
           f.natDegree * (M * x ^ (f.natDegree - 1)) by
    have hxpow : x ^ f.natDegree = x * x ^ (f.natDegree - 1) := by
      rw [← pow_succ', show f.natDegree - 1 + 1 = f.natDegree by omega]
    linear_combination this + hxpow * f.leadingCoeff
  suffices ∀ i < f.natDegree, f.coeff i * x ^ i ≤ M * x ^ (f.natDegree - 1) by
    simpa using sum_le_card_nsmul (range f.natDegree) (fun i ↦ f.coeff i * x ^ i) _ <|
      by simpa using this
  intro i hi
  rw [← Even.pow_abs <| Nat.Odd.sub_odd hdeg (by simp)]
  calc
    f.coeff i * x ^ i ≤ |f.coeff i| * |x| ^ i := by
      rw [← abs_pow, ← abs_mul]
      exact le_abs_self ..
    _ ≤ M * |x| ^ (f.natDegree - 1) := by
      gcongr; exacts [hM _ hi, by simpa using abs_le_abs_of_nonpos (by linarith) hx, by omega]

variable {f} in
theorem eventually_neg (hdeg : Odd f.natDegree) (hf : 0 < f.leadingCoeff) :
    ∃ y : F, ∀ x, x < y → f.eval x < 0 := by
  set z := (Finset.image (|f.coeff ·|) (Finset.range f.natDegree)).max'
    (by simpa using Nat.ne_of_odd_add hdeg)
  use min (-1) (-f.natDegree * z / f.leadingCoeff)
  intro x hx
  have one_lt_x : x < -1 := lt_of_lt_of_le hx (min_le_left ..)
  have : 0 < x ^ (f.natDegree - 1) := by
    rw [← Even.pow_abs <| Nat.Odd.sub_odd hdeg (by simp)]
    have : 1 ≤ |x| := by simpa using abs_le_abs_of_nonpos (by linarith) (by linarith: x ≤ -1)
    positivity
  have := calc
    f.eval x ≤ x ^ (f.natDegree - 1) * (f.leadingCoeff * x + f.natDegree * z) :=
      estimate2 hdeg (le_of_lt one_lt_x)
    _ < x ^ (f.natDegree - 1) * (f.leadingCoeff * (min (-1) (-f.natDegree * z / f.leadingCoeff)) +
        f.natDegree * z) := by gcongr
    _ ≤ x ^ (f.natDegree - 1) * (f.leadingCoeff * (-f.natDegree * z / f.leadingCoeff) +
        f.natDegree * z) := by gcongr; exact min_le_right ..
  field_simp at this
  ring_nf at this
  assumption

variable {f} in
theorem sign_change (hdeg: Odd f.natDegree) : ∃ x y, f.eval x < 0 ∧ 0 < f.eval y := by
  wlog hf : 0 < f.leadingCoeff generalizing f with res
  · have : f.leadingCoeff ≠ 0 := by
      simpa using ne_of_apply_ne natDegree (Nat.ne_of_odd_add hdeg : f.natDegree ≠ 0)
    have : 0 < (-f).leadingCoeff := by
      simpa [-leadingCoeff_eq_zero] using lt_of_le_of_ne (by simpa using hf) this
    rcases res (by simpa using hdeg) this with ⟨x, y, hx, hy⟩
    exact ⟨y, x, by simp_all⟩
  · rcases eventually_pos (Nat.ne_of_odd_add hdeg) hf with ⟨x, hx⟩
    rcases eventually_neg hdeg hf with ⟨y, hy⟩
    exact ⟨y-1, x+1, hy _ (by linarith), hx _ (by linarith)⟩

#min_imports
