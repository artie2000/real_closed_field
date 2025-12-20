/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.PrimitiveElement.Instances

namespace Algebra.IsIntegralUniqueGen.Quadratic

open _root_.Polynomial
open Algebra
open scoped algebraMap

variable {K L : Type*} [CommRing K] [Ring L] [Algebra K L]
         {a : K} {r : L} (hr : Algebra.IsIntegralUniqueGen r (X ^ 2 - C a))

include hr in
theorem sq_root : r ^ 2 = a := by
  suffices r ^ 2 - a = 0 by grind
  simpa using hr.aeval_self

variable [Nontrivial K]

instance : NeZero (X ^ 2 - C a).natDegree := ⟨by simp⟩

include hr in
theorem nontrivial : Nontrivial L := hr.nontrivial (by apply_fun natDegree; simp)

include hr in
theorem isQuadraticExtension : Algebra.IsQuadraticExtension K L where
  __ := hr.free
  finrank_eq_two' := by simpa using hr.finrank_eq_natDegree

theorem basis_0 : hr.basis 0 = 1 := by simp

theorem basis_1 : hr.basis 1 = r := by simp

@[simp]
theorem coeff_one : hr.coeff 1 = Pi.single 0 1 :=
  letI _ := nontrivial hr
  hr.coeff_one

@[simp]
theorem coeff_root : hr.coeff r = Pi.single 1 1 := hr.coeff_root (by simp)

@[simp]
theorem coeff_algebraMap (k : K) : hr.coeff k = Pi.single 0 k :=
  letI _ := nontrivial hr
  hr.coeff_algebraMap k

@[simp]
theorem coeff_ofNat (n : ℕ) [Nat.AtLeastTwo n] : hr.coeff ofNat(n) = Pi.single 0 (n : K) :=
  letI _ := nontrivial hr
  hr.coeff_ofNat n

theorem self_eq_coeff (x) :
    x = hr.coeff x 0 + hr.coeff x 1 * r := by
  rw [hr.ext_elem_iff]
  intro i hi
  have : i < 2 := by simpa using hi
  interval_cases i <;> simp [← Algebra.smul_def]

theorem coeff_of_add_of_mul_root {x y : K} :
    hr.coeff (x + y * r) = fun₀ | 0 => x | 1 => y := by
  ext i
  by_cases h : i < 2
  · interval_cases i <;> simp [← Algebra.smul_def]
  · rw [show hr.coeff _ i = 0 from hr.coeff_apply_of_natDegree_le _ i (by simpa using h)]
    simp [show 0 ≠ i ∧ i ≠ 1 by omega]

@[simp]
theorem coeff_mul {K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Nontrivial K]
         {a : K} {r : L} (hr : Algebra.IsIntegralUniqueGen r (X ^ 2 - C a))
         (x y) : hr.coeff (x * y) =
    fun₀
    | 0 => hr.coeff x 0 * hr.coeff y 0 + a * hr.coeff x 1 * hr.coeff y 1
    | 1 => hr.coeff x 0 * hr.coeff y 1 + hr.coeff y 0 * hr.coeff x 1 := by
  rw [← coeff_of_add_of_mul_root hr]
  congr
  nth_rw 1 [self_eq_coeff hr x, self_eq_coeff hr y]
  ring_nf
  simp only [sq_root hr, map_add, map_mul]
  ring

end Algebra.IsIntegralUniqueGen.Quadratic

open Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

open Polynomial in
theorem X_sq_sub_C_irreducible_iff_not_isSquare {F : Type*} [Field F] (a : F) :
    Irreducible (X ^ 2 - C a) ↔ ¬ IsSquare a := by
  rw [isSquare_iff_exists_sq, X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two]
  grind only

theorem exists_gen [Algebra.IsQuadraticExtension K L] :
    ∃ a : K, IsAdjoinRootMonic' L (X ^ 2 - C a) := by
  sorry

theorem related_gen {r₁ r₂ : L} {a₁ a₂ : K}
    (h₁ : Algebra.IsIntegralUniqueGen r₁ (X ^ 2 - C a₁))
    (h₂ : Algebra.IsIntegralUniqueGen r₂ (X ^ 2 - C a₂)) : IsSquare (a₁ / a₂) := by
  sorry

theorem gen_of_isSquare {r₁ : L} {a₁ a₂ : K}
    (ha : IsSquare (a₁ / a₂))
    (h : Algebra.IsIntegralUniqueGen r₁ (X ^ 2 - C a₁)) :
    IsAdjoinRootMonic' L (X ^ 2 - C a₂) where
  exists_root := by
    rcases ha with ⟨m, hm⟩
    use (algebraMap _ _ m) * r₁
    -- ↑m * r₁ generates since r₁ generates
    -- ↑m * r₁ satisfies X ^ 2 - C (m * a₁) = X ^ 2 - C a₂, which is irreducible, so done
  f_monic := by simp [Monic]
