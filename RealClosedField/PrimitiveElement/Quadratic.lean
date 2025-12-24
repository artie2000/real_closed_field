/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.PrimitiveElement.Instances
import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.Data.Finsupp.Notation
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

open Polynomial
open Algebra
open scoped algebraMap

-- TODO : generalise to `n`th root?
structure IsIntegralGenSqrt {K L : Type*} [CommRing K] [Ring L] [Algebra K L] (r : L) (a : K)
    extends IsIntegralUniqueGen r (X ^ 2 - C a)

namespace IsIntegralGenSqrt

variable {K L : Type*} [CommRing K] [Ring L] [Algebra K L]
         {a : K} {r : L} (h : IsIntegralGenSqrt r a)

include h in
theorem sq_root : r ^ 2 = a := by
  suffices r ^ 2 - a = 0 by grind
  simpa using h.aeval_gen

variable [Nontrivial K]

instance : NeZero (X ^ 2 - C a).natDegree := ⟨by simp⟩

include h in
theorem nontrivial : Nontrivial L :=
  h.toIsIntegralUnique.nontrivial (by apply_fun natDegree; simp)

include h in
theorem isQuadraticExtension :
    Algebra.IsQuadraticExtension K L where
  __ := h.free
  finrank_eq_two' := by simpa using h.finrank_eq_natDegree

theorem basis_0 : h.basis 0 = 1 := by simp

theorem basis_1 : h.basis 1 = r := by simp

@[simp]
theorem coeff_one : h.coeff 1 = Pi.single 0 1 :=
  letI _ := h.nontrivial
  h.toIsIntegralUniqueGen.coeff_one

@[simp]
theorem coeff_root : h.coeff r = Pi.single 1 1 :=
  h.toIsIntegralUniqueGen.coeff_root (by simp)

@[simp]
theorem coeff_algebraMap (k : K) : h.coeff (algebraMap _ _ k) = Pi.single 0 k :=
  letI _ := h.nontrivial
  h.toIsIntegralUniqueGen.coeff_algebraMap k

@[simp]
theorem coeff_ofNat (n : ℕ) [Nat.AtLeastTwo n] : h.coeff ofNat(n) = Pi.single 0 (n : K) :=
  letI _ := h.nontrivial
  h.toIsIntegralUniqueGen.coeff_ofNat n

set_option trace.Meta.Tactic.simp true
theorem foo : h.coeff r = Pi.single 1 1 := by simp

theorem self_eq_coeff (x : L) : x = algebraMap _ _ (h.coeff x 0) + algebraMap _ _ (h.coeff x 1) * r := by
  rw [h.ext_elem_iff]
  intro i hi
  have : i < 2 := by simpa using hi
  interval_cases i <;> simp [← Algebra.smul_def]

theorem coeff_of_add_of_mul_root {x y : K} : h.coeff (x + y * r) = fun₀ | 0 => x | 1 => y := by
  ext i
  by_cases hi : i < 2
  · interval_cases i <;> simp [← Algebra.smul_def]
  · rw [show h.coeff _ i = 0 from h.coeff_apply_of_natDegree_le _ i (by simpa using hi)]
    simp [show i ≠ 0 ∧ i ≠ 1 by omega]

@[simp]
theorem coeff_mul {K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Nontrivial K]
         {a : K} {r : L} (h : IsIntegralGenSqrt r a) (x y) :
    h.coeff (x * y) =
    fun₀
    | 0 => h.coeff x 0 * h.coeff y 0 + a * h.coeff x 1 * h.coeff y 1
    | 1 => h.coeff x 0 * h.coeff y 1 + h.coeff y 0 * h.coeff x 1 := by
  rw [← coeff_of_add_of_mul_root h]
  congr
  nth_rw 1 [self_eq_coeff h x, self_eq_coeff h y]
  ring_nf
  simp only [h.sq_root, map_add, map_mul]
  ring

@[simp]
theorem coeff_pow_two {K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Nontrivial K]
         {a : K} {r : L} (h : IsIntegralGenSqrt r a) (x) :
    h.coeff (x ^ 2) =
    fun₀
    | 0 => h.coeff x 0 ^ 2 + a * h.coeff x 1 ^ 2
    | 1 => 2 * h.coeff x 0 * h.coeff x 1 := by
  simp [pow_two x]
  ext i
  by_cases h : i < 2
  · interval_cases i <;> simp <;> ring
  · simp [show i ≠ 0 ∧ i ≠ 1 by omega]

end IsIntegralGenSqrt

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem Polynomial.X_sq_sub_C_irreducible_iff_not_isSquare {F : Type*} [Field F] (a : F) :
    Irreducible (X ^ 2 - C a) ↔ ¬ IsSquare a := by
  rw [isSquare_iff_exists_sq, X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two]
  grind only

theorem IsIntegralUniqueGen.SqRoot.not_isSquare {a : K} {r : L}
    (h : IsIntegralUnique r (X ^ 2 - C a)) : ¬ IsSquare a := by
  simpa [X_sq_sub_C_irreducible_iff_not_isSquare] using h.irreducible_gen

theorem IsIntegralUniqueGen.SqRoot.ne_zero {a : K} {r : L}
    (h : IsIntegralUnique r (X ^ 2 - C a)) : a ≠ 0 := fun hc ↦
      IsIntegralUniqueGen.SqRoot.not_isSquare h (by aesop)

theorem IsIntegralUnique.of_square_root {a : K} (ha : ¬ IsSquare a)
    {r : L} (h : r ^ 2 = algebraMap _ _ a) : IsIntegralUnique r (X ^ 2 - C a) := by
  have root : (X ^ 2 - C a).aeval r = 0 := by simp [h]
  have monic : (X ^ 2 - C a).Monic := by simp [Monic]
  convert IsIntegrallyClosed.isIntegralUnique ⟨_, monic, root⟩
  rw [← X_sq_sub_C_irreducible_iff_not_isSquare] at ha
  exact minpoly.eq_of_irreducible_of_monic ha root monic

theorem generator_of_notMem_bot [Algebra.IsQuadraticExtension K L] {r : L}
    (h : r ∉ (⊥ : Subalgebra K L)) : IsGenerator K r where
  adjoin_eq_top := by
    have : adjoin K {r} ≠ ⊥ := fun hc ↦ h <| by
      simpa [← hc] using self_mem_adjoin_singleton K r
    have := (Subalgebra.isSimpleOrder_of_finrank_prime K L
      (by simpa [Algebra.IsQuadraticExtension.finrank_eq_two] using Nat.prime_two)).eq_bot_or_eq_top
        (adjoin K {r})
    grind
    -- TODO : fix proof

theorem IsIntegralUniqueGen.of_square_root [Algebra.IsQuadraticExtension K L]
    {a : K} {r : L} (h₁ : r ∉ (⊥ : Subalgebra K L))
    (h₂ : r ^ 2 = algebraMap _ _ a) : IsIntegralUniqueGen r (X ^ 2 - C a) where
  __ : IsIntegralUnique .. := by
    refine .of_square_root (fun ⟨r', h'⟩ ↦ ?_) h₂
    apply_fun algebraMap _ L at h'
    rw [h', map_mul, ← pow_two] at h₂
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ h₂ with (h | h) <;> simp_all
  __ := generator_of_notMem_bot h₁

theorem exists_gen [Algebra.IsQuadraticExtension K L] (hK : ringChar K ≠ 2) :
    ∃ a : K, IsAdjoinRootMonic' L (X ^ 2 - C a) := by
  have : (⊥ : Subalgebra K L) ≠ ⊤ := by
    simp [Subalgebra.bot_eq_top_iff_finrank_eq_one, Algebra.IsQuadraticExtension.finrank_eq_two]
  rcases SetLike.exists_not_mem_of_ne_top ⊥ this rfl with ⟨s, hs⟩
  have h : IsIntegralUniqueGen s _ := {
    IsIntegrallyClosed.isIntegralUnique (Algebra.IsIntegral.isIntegral (R := K) s),
    generator_of_notMem_bot hs with }
  have sdeg : (minpoly K s).natDegree = 2 := by
    rw [← h.finrank_eq_natDegree, Algebra.IsQuadraticExtension.finrank_eq_two]
  use ((h.coeff (s ^ 2) 1) ^ 2 + 4 * h.coeff (s ^ 2) 0)
  refine .ofIsIntegralUniqueGen (x := 2 * s - algebraMap _ _ (h.coeff (s ^ 2) 1))
    (.of_square_root (fun hc ↦ hs ?_) ?_)
  · simp [Algebra.mem_bot] at hc
    rcases hc with ⟨b, hb⟩
    have : s = (algebraMap K L) ((b + h.coeff (s ^ 2) 1) / 2) := by
      simp [map_ofNat]
      have : (2 : L) ≠ 0 := Ring.two_ne_zero (by simpa [Algebra.ringChar_eq K L] using hK)
      linear_combination (norm := (field_simp; ring)) - hb / 2
    rw [this]
    exact Subalgebra.algebraMap_mem ..
  · have : s ^ 2 =
        (algebraMap _ _ (h.coeff (s ^ 2) 1)) * s + (algebraMap _ _ (h.coeff (s ^ 2) 0)) := by
      have lc : (minpoly K s).coeff 2 = 1 := by simpa [sdeg] using h.monic.coeff_natDegree
      have scoeff : ∀ i < 2, h.coeff (s ^ 2) i = - (minpoly K s).coeff i := fun _ _ ↦ by
        simpa [sdeg] using h.coeff_root_pow_natDegree (by simpa [sdeg])
      have := by simpa [↓Polynomial.aeval_eq_sum_range, ← h.finrank_eq_natDegree,
        Algebra.IsQuadraticExtension.finrank_eq_two, Finset.sum_range_succ, smul_def, lc] using
          minpoly.aeval K s
      simp [scoeff]
      linear_combination this
    ring_nf
    nth_rw 2 [this]
    simp [map_ofNat]
    ring

theorem related_gen {r₁ r₂ : L} {a₁ a₂ : K} (hK : ringChar K ≠ 2)
    (h₁ : IsIntegralUniqueGen r₁ (X ^ 2 - C a₁))
    (h₂ : IsIntegralUniqueGen r₂ (X ^ 2 - C a₂)) : IsSquare (a₁ / a₂) := by
  have : a₂ ≠ 0 := IsIntegralUniqueGen.SqRoot.ne_zero h₂.toIsIntegralUnique
  have eq : r₂ ^ 2 = algebraMap _ _ a₂ := IsIntegralUniqueGen.SqRoot.sq_root h₂.toIsIntegralUnique
  have c0 : h₁.coeff r₂ 0 ^ 2 + a₁ * h₁.coeff r₂ 1 ^ 2 = a₂ := by
    apply_fun (h₁.coeff · 0) at eq
    simpa using eq
  rcases show h₁.coeff r₂ 0 = 0 ∨ h₁.coeff r₂ 1 = 0 by
    apply_fun (h₁.coeff · 1) at eq
    simpa [Ring.two_ne_zero hK] using eq
  with (h0 | h1)
  · use (h₁.coeff r₂ 1)⁻¹
    have : h₁.coeff r₂ 1 ≠ 0 := fun hc ↦
      IsIntegralUniqueGen.SqRoot.ne_zero h₂.toIsIntegralUnique (by simp_all)
    field_simp
    simp_all
  · absurd IsIntegralUniqueGen.SqRoot.not_isSquare h₂.toIsIntegralUnique
    exact ⟨h₁.coeff r₂ 0, by simp_all [pow_two]⟩

theorem related_isAdjoinRoot {a₁ a₂ : K} (hK : ringChar K ≠ 2)
    (h₁ : IsAdjoinRootMonic' L (X ^ 2 - C a₁))
    (h₂ : IsAdjoinRootMonic' L (X ^ 2 - C a₂)) : IsSquare (a₁ / a₂) :=
  related_gen hK h₁.pe h₂.pe

theorem gen_of_isSquare {r₁ : L} {a₁ a₂ : K} (ha₂ : a₂ ≠ 0)
    (ha : IsSquare (a₁ / a₂))
    (h : IsIntegralUniqueGen r₁ (X ^ 2 - C a₁)) :
    IsAdjoinRootMonic' L (X ^ 2 - C a₂) where
  exists_root := by
    rcases ha with ⟨m, hm⟩
    field_simp at hm
    have mz : m ≠ 0 := fun hc ↦
      IsIntegralUniqueGen.SqRoot.ne_zero h.toIsIntegralUnique (by simp_all)
    use (algebraMap _ _ m⁻¹) * r₁
    refine { IsIntegralUnique.of_square_root (fun hc ↦ ?_) ?_,
            h.algberaMap_mul (inv_ne_zero mz) with }
    · have : IsSquare a₁ := by aesop
      exact IsIntegralUniqueGen.SqRoot.not_isSquare h.toIsIntegralUnique this
    · calc
        (algebraMap _ _ m⁻¹ * r₁) ^ 2 = algebraMap _ _ m⁻¹ ^ 2 * r₁ ^ 2 := by ring
        _ = algebraMap _ _ (m⁻¹ ^ 2 * a₁) := by
          simp [IsIntegralUniqueGen.SqRoot.sq_root h.toIsIntegralUnique]
        _ = algebraMap _ _ a₂ := by rw [hm]; field_simp
  f_monic := by simp [Monic]

-- TODO : figure out how to define this!
@[simps]
noncomputable def deg_2_classify (hK : ringChar K ≠ 2) :
    (Kˣ ⧸ (Subgroup.square Kˣ)) ≃
    { L : IntermediateField K (AlgebraicClosure K) // Algebra.IsQuadraticExtension K L } where
  toFun := Quotient.lift
    (fun a ↦ sorry)--(⊤ : IntermediateField K (AdjoinRoot (X ^ 2 - C (a : K)))).map IsAlgClosed.lift)
    (fun a₁ a₂ ha ↦ by sorry)
  invFun L :=
    have ⟨L, hL⟩ := L;
    ⟦.mk0 (Classical.choose (exists_gen hK (L := L)))
      (IsIntegralUniqueGen.SqRoot.ne_zero
        (Classical.choose_spec (exists_gen hK (L := L))).pe.toIsIntegralUnique)⟧
  left_inv := sorry
  right_inv := sorry

#min_imports
