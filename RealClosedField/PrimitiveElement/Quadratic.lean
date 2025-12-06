/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.PrimitiveElement.PrimitiveElement
import Mathlib.Data.Finsupp.Notation

namespace IsAdjoinRoot.Quadratic

open _root_.Polynomial
open Algebra
open scoped algebraMap

variable {K L : Type*} [CommRing K] [CommRing L] [Algebra K L]
         {a : K} {r : L} (hr : Algebra.HasPrincipalKerAevalIntegral K r)
         (hr₂ : minpoly K r = X ^ 2 - C a)

include hr hr₂ in
theorem sq_root : r ^ 2 = a := by
  suffices r ^ 2 - a = 0 by grind
  simpa [hr₂] using hr.aeval_self

variable [Nontrivial K]

--instance : NeZero (minpoly K r).natDegree := ⟨by simp [hr₂]⟩

include hr₂ in
theorem nontrivial : Nontrivial L := by
  contrapose! hr₂
  apply_fun natDegree
  simp [nontriviality]

include hr hr₂ in
theorem isQuadraticExtension : Algebra.IsQuadraticExtension K L where
  __ := hr.free
  finrank_eq_two' := by simpa [hr₂] using hr.finrank_eq_natDegree

--include hr₂ in
--theorem basis_0 : hr.basis 0 = 1 := by simp

--theorem basis_1 : hr.basis 1 = r := by simp

include hr₂ in
@[simp]
theorem coeff_one : hr.coeff 1 = Pi.single 0 1 :=
  letI _ := nontrivial hr₂
  hr.coeff_one

include hr₂ in
@[simp]
theorem coeff_root : hr.coeff r = Pi.single 1 1 := hr.coeff_root (by simp [hr₂])

include hr₂ in
@[simp]
theorem coeff_algebraMap (k : K) : hr.coeff k = Pi.single 0 k :=
  letI _ := nontrivial hr₂
  hr.coeff_algebraMap k

include hr₂ in
@[simp]
theorem coeff_ofNat (n : ℕ) [Nat.AtLeastTwo n] : hr.coeff ofNat(n) = Pi.single 0 (n : K) :=
  letI _ := nontrivial hr₂
  hr.coeff_ofNat n

include hr₂ in
theorem self_eq_coeff (x) :
    x = hr.coeff x 0 + hr.coeff x 1 * r := by
  rw [hr.ext_elem_iff]
  intro i hi
  have : i < 2 := by simpa [hr₂] using hi
  interval_cases i <;> simp [← Algebra.smul_def, hr₂]

include hr₂ in
theorem coeff_of_add_of_mul_root {x y : K} :
    hr.coeff (x + y * r) = fun₀ | 0 => x | 1 => y := by
  ext i
  by_cases h : i < 2
  · interval_cases i <;> simp [← Algebra.smul_def, hr₂]
  · rw [show hr.coeff _ i = 0 from hr.coeff_apply_of_natDegree_le _ i (by simpa [hr₂] using h)]
    simp [show 0 ≠ i ∧ i ≠ 1 by omega]

include hr₂ in
@[simp]
theorem coeff_mul (x y) : hr.coeff (x * y) =
    fun₀
    | 0 => hr.coeff x 0 * hr.coeff y 0 + a * hr.coeff x 1 * hr.coeff y 1
    | 1 => hr.coeff x 0 * hr.coeff y 1 + hr.coeff y 0 * hr.coeff x 1 := by
  rw [← coeff_of_add_of_mul_root hr hr₂]
  congr
  nth_rw 1 [self_eq_coeff hr hr₂ x, self_eq_coeff hr hr₂ y]
  ring_nf
  simp only [sq_root hr hr₂, map_add, map_mul]
  ring

end IsAdjoinRoot.Quadratic
