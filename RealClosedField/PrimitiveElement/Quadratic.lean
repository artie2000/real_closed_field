/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.PrimitiveElement.PrimitiveElement

namespace IsAdjoinRoot.Quadratic

open _root_.Polynomial
open Algebra
open scoped algebraMap

variable {K L : Type*} [CommRing K] [CommRing L] [Algebra K L]
         {a : K} {x : L} (hx : Algebra.HasPrincipalKerAevalIntegral K x)
         (hx₂ : minpoly K x = X ^ 2 - C a)


include hx hx₂ in
@[simp]
theorem sq_root : x ^ 2 = a := by
  suffices x ^ 2 - a = 0 by grind
  simpa [hx₂] using hx.aeval_self

variable [Nontrivial K]

instance : NeZero (X ^ 2 - C a).natDegree := ⟨by simp⟩

include hx in
theorem nontrivial : Nontrivial L := hx.nontrivial (by apply_fun natDegree; simp)

include hL in
theorem isQuadraticExtension : Algebra.IsQuadraticExtension K L where
  __ := Module.Free.of_basis hL.basis
  finrank_eq_two' := by simpa using hL.finrank

theorem basis_0 : hL.basis 0 = 1 := by simp

theorem basis_1 : hL.basis 1 = √a := by simp

@[simp]
theorem coeff_one : hL.coeff 1 = Pi.single 0 1 :=
  letI _ := nontrivial hL
  hL.coeff_one

@[simp]
theorem coeff_root : hL.coeff √a = Pi.single 1 1 := hL.coeff_root (by simp)

@[simp]
theorem coeff_algebraMap (x : K) : hL.coeff x = Pi.single 0 x :=
  letI _ := nontrivial hL
  hL.coeff_algebraMap x

@[simp]
theorem coeff_ofNat (n : ℕ) [Nat.AtLeastTwo n] : hL.coeff ofNat(n) = Pi.single 0 (n : K) :=
  letI _ := nontrivial hL
  hL.coeff_ofNat n

theorem self_eq_coeff (x) :
    x = hL.coeff x 0 + hL.coeff x 1 * √a := by
  rw [hL.ext_elem_iff]
  intro i hi
  simp_rw [show (X ^ 2 - C a).natDegree = 2 by simp] at hi
  interval_cases i <;> simp [← Algebra.smul_def]

theorem coeff_of_add_of_mul_root {x y : K} :
    hL.coeff (x + y * (√a)) = fun₀ | 0 => x | 1 => y := by
  ext i
  by_cases h : i < 2
  · interval_cases i <;> simp [← Algebra.smul_def]
  · rw [show hL.coeff _ i = 0 from hL.coeff_apply_le _ i (by simpa using h)]
    simp [show 0 ≠ i ∧ i ≠ 1 by omega]

@[simp]
theorem coeff_mul (x y) : hL.coeff (x * y) =
    fun₀
    | 0 => hL.coeff x 0 * hL.coeff y 0 + a * hL.coeff x 1 * hL.coeff y 1
    | 1 => hL.coeff x 0 * hL.coeff y 1 + hL.coeff y 0 * hL.coeff x 1 := by
  rw [← coeff_of_add_of_mul_root hL]
  congr
  nth_rw 1 [self_eq_coeff hL x, self_eq_coeff hL y]
  ring_nf
  simp only [sq_root, map_mul, map_add]
  ring

end IsAdjoinRoot.Quadratic
