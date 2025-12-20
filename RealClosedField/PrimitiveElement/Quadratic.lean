/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.PrimitiveElement.Instances

open Polynomial
open Algebra
open scoped algebraMap

namespace IsIntegralUniqueGen.SqRoot

variable {K L : Type*} [CommRing K] [Ring L] [Algebra K L]
         {a : K} {r : L}

theorem sq_root (hr : IsIntegralUnique r (X ^ 2 - C a)) : r ^ 2 = a := by
  suffices r ^ 2 - a = 0 by grind
  simpa using hr.aeval_gen

variable [Nontrivial K]

instance : NeZero (X ^ 2 - C a).natDegree := ⟨by simp⟩

theorem nontrivial (hr : IsIntegralUnique r (X ^ 2 - C a)) : Nontrivial L :=
  hr.nontrivial (by apply_fun natDegree; simp)

theorem isQuadraticExtension (hr : IsIntegralUniqueGen r (X ^ 2 - C a)) :
    Algebra.IsQuadraticExtension K L where
  __ := hr.free
  finrank_eq_two' := by simpa using hr.finrank_eq_natDegree

theorem basis_0 (hr : IsIntegralUniqueGen r (X ^ 2 - C a)) : hr.basis 0 = 1 := by simp

theorem basis_1 (hr : IsIntegralUniqueGen r (X ^ 2 - C a)) : hr.basis 1 = r := by simp

@[simp]
theorem coeff_one (hr : IsIntegralUniqueGen r (X ^ 2 - C a)) : hr.coeff 1 = Pi.single 0 1 :=
  letI _ := nontrivial hr.toIsIntegralUnique
  hr.coeff_one

@[simp]
theorem coeff_root (hr : IsIntegralUniqueGen r (X ^ 2 - C a)) : hr.coeff r = Pi.single 1 1 :=
  hr.coeff_root (by simp)

@[simp]
theorem coeff_algebraMap (hr : IsIntegralUniqueGen r (X ^ 2 - C a)) (k : K) :
    hr.coeff k = Pi.single 0 k :=
  letI _ := nontrivial hr.toIsIntegralUnique
  hr.coeff_algebraMap k

@[simp]
theorem coeff_ofNat (hr : IsIntegralUniqueGen r (X ^ 2 - C a)) (n : ℕ) [Nat.AtLeastTwo n] :
    hr.coeff ofNat(n) = Pi.single 0 (n : K) :=
  letI _ := nontrivial hr.toIsIntegralUnique
  hr.coeff_ofNat n

theorem self_eq_coeff (hr : IsIntegralUniqueGen r ((X ^ 2 - C a) : K[X])) (x : L) :
    x = hr.coeff x 0 + hr.coeff x 1 * r := by
  rw [hr.ext_elem_iff]
  intro i hi
  have : i < 2 := by simpa using hi
  interval_cases i <;> simp [← Algebra.smul_def]

theorem coeff_of_add_of_mul_root (hr : IsIntegralUniqueGen r (X ^ 2 - C a)) {x y : K} :
    hr.coeff (x + y * r) = fun₀ | 0 => x | 1 => y := by
  ext i
  by_cases h : i < 2
  · interval_cases i <;> simp [← Algebra.smul_def]
  · rw [show hr.coeff _ i = 0 from hr.coeff_apply_of_natDegree_le _ i (by simpa using h)]
    simp [show i ≠ 0 ∧ i ≠ 1 by omega]

@[simp]
theorem coeff_mul {K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Nontrivial K]
         {a : K} {r : L} (hr : IsIntegralUniqueGen r (X ^ 2 - C a))
         (x y) : hr.coeff (x * y) =
    fun₀
    | 0 => hr.coeff x 0 * hr.coeff y 0 + a * hr.coeff x 1 * hr.coeff y 1
    | 1 => hr.coeff x 0 * hr.coeff y 1 + hr.coeff y 0 * hr.coeff x 1 := by
  rw [← coeff_of_add_of_mul_root hr]
  congr
  nth_rw 1 [self_eq_coeff hr x, self_eq_coeff hr y]
  ring_nf
  simp only [sq_root hr.toIsIntegralUnique, map_add, map_mul]
  ring

@[simp]
theorem coeff_pow_two {K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Nontrivial K]
         {a : K} {r : L} (hr : IsIntegralUniqueGen r (X ^ 2 - C a))
         (x) : hr.coeff (x ^ 2) =
    fun₀
    | 0 => hr.coeff x 0 ^ 2 + a * hr.coeff x 1 ^ 2
    | 1 => 2 * hr.coeff x 0 * hr.coeff x 1 := by
  simp [pow_two x]
  ext i
  by_cases h : i < 2
  · interval_cases i <;> simp <;> ring
  · simp [show i ≠ 0 ∧ i ≠ 1 by omega]

end IsIntegralUniqueGen.SqRoot

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem Polynomial.X_sq_sub_C_irreducible_iff_not_isSquare {F : Type*} [Field F] (a : F) :
    Irreducible (X ^ 2 - C a) ↔ ¬ IsSquare a := by
  rw [isSquare_iff_exists_sq, X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two]
  grind only

theorem IsIntegralUniqueGen.SqRoot.not_isSquare {a : K} {r : L}
    (hr : IsIntegralUnique r (X ^ 2 - C a)) : ¬ IsSquare a := by
  simpa [X_sq_sub_C_irreducible_iff_not_isSquare] using hr.gen_irreducible

theorem IsIntegralUniqueGen.SqRoot.ne_zero {a : K} {r : L}
    (hr : IsIntegralUnique r (X ^ 2 - C a)) : a ≠ 0 := fun hc ↦
      IsIntegralUniqueGen.SqRoot.not_isSquare hr (by aesop)

theorem IsIntegralUnique.of_square_root {a : K} (ha : ¬ IsSquare a)
    {r : L} (hr : r ^ 2 = algebraMap _ _ a) : IsIntegralUnique r (X ^ 2 - C a) := by
  have root : aeval r (X ^ 2 - C a) = 0 := by simp [hr]
  have monic : (X ^ 2 - C a).Monic := by simp [Monic]
  convert IsIntegrallyClosed.isIntegralUnique ⟨_, monic, root⟩
  rw [← X_sq_sub_C_irreducible_iff_not_isSquare] at ha
  exact minpoly.eq_of_irreducible_of_monic ha root monic
  -- TODO : figure out how to avoid duplication in this proof

theorem exists_gen [Algebra.IsQuadraticExtension K L] :
    ∃ a : K, IsAdjoinRootMonic' L (X ^ 2 - C a) := by
  sorry

theorem related_gen {r₁ r₂ : L} {a₁ a₂ : K}  [NeZero (2 : K)]
    (h₁ : IsIntegralUniqueGen r₁ (X ^ 2 - C a₁))
    (h₂ : IsIntegralUniqueGen r₂ (X ^ 2 - C a₂)) : IsSquare (a₁ / a₂) := by
  have : a₂ ≠ 0 := IsIntegralUniqueGen.SqRoot.ne_zero h₂.toIsIntegralUnique
  have eq : r₂ ^ 2 = algebraMap _ _ a₂ := IsIntegralUniqueGen.SqRoot.sq_root h₂.toIsIntegralUnique
  have c0 : h₁.coeff r₂ 0 ^ 2 + a₁ * h₁.coeff r₂ 1 ^ 2 = a₂ := by
    apply_fun (h₁.coeff · 0) at eq
    simpa using eq
  rcases show h₁.coeff r₂ 0 = 0 ∨ h₁.coeff r₂ 1 = 0 by
    apply_fun (h₁.coeff · 1) at eq
    simpa [two_ne_zero] using eq
  with (h0 | h1)
  · use (h₁.coeff r₂ 1)⁻¹
    have : h₁.coeff r₂ 1 ≠ 0 := fun hc ↦
      IsIntegralUniqueGen.SqRoot.ne_zero h₂.toIsIntegralUnique (by simp_all)
    field_simp
    simp_all
  · absurd IsIntegralUniqueGen.SqRoot.not_isSquare h₂.toIsIntegralUnique
    exact ⟨h₁.coeff r₂ 0, by simp_all [pow_two]⟩

theorem gen_of_isSquare {r₁ : L} {a₁ a₂ : K} (ha₂ : a₂ ≠ 0)
    (ha : IsSquare (a₁ / a₂))
    (h : IsIntegralUniqueGen r₁ (X ^ 2 - C a₁)) :
    IsAdjoinRootMonic' L (X ^ 2 - C a₂) where
  exists_root := by
    rcases ha with ⟨m, hm⟩
    field_simp at hm
    have : m ≠ 0 := fun hc ↦
      IsIntegralUniqueGen.SqRoot.ne_zero h.toIsIntegralUnique (by simp_all)
    use (algebraMap _ _ m⁻¹) * r₁
    refine { (?_ : IsIntegralUnique ..), (?_ : IsGenerator ..) with }
    · refine IsIntegralUnique.of_square_root (fun hc ↦ ?_) ?_
      · have : IsSquare a₁ := by aesop
        exact IsIntegralUniqueGen.SqRoot.not_isSquare h.toIsIntegralUnique this
      · calc
          (algebraMap _ _ m⁻¹ * r₁) ^ 2 = algebraMap _ _ m⁻¹ ^ 2 * r₁ ^ 2 := by ring
          _ = algebraMap _ _ (m⁻¹ ^ 2 * a₁) := by
            simp [IsIntegralUniqueGen.SqRoot.sq_root h.toIsIntegralUnique]
          _ = algebraMap _ _ a₂ := by rw [hm]; field_simp
    · exact .of_root_mem_adjoin h.toIsGenerator <| by
        nth_rw 2 [show r₁ = m • ((algebraMap _ _ m⁻¹) * r₁) by
          rw [smul_def, ← mul_assoc, ← map_mul]
          simp [this]]
        exact Subalgebra.smul_mem (adjoin K {(algebraMap K L) m⁻¹ * r₁})
          (x := (algebraMap K L) m⁻¹ * r₁) (by aesop) m
      -- TODO : fix proof
  f_monic := by simp [Monic]
