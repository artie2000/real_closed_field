/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.PrimitiveElement.Instances
import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.Data.Finsupp.Notation
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

-- TODO : upstream
theorem Polynomial.X_sq_sub_C_irreducible_iff_not_isSquare {F : Type*} [Field F] (a : F) :
    Irreducible (X ^ 2 - C a) ↔ ¬ IsSquare a := by
  rw [isSquare_iff_exists_sq, X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two]
  grind only

open Polynomial
open Algebra

-- TODO : generalise to `n`th root?
structure IsIntegralGenSqrt {R S : Type*} [CommRing R] [Ring S] [Algebra R S] (r : S) (a : R)
    extends IsIntegralUniqueGen r (X ^ 2 - C a)

namespace IsIntegralGenSqrt

section Ring

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
         {r : S} {a : R} (h : IsIntegralGenSqrt r a)

include h in
theorem sq_root : r ^ 2 = algebraMap _ _ a := by
  suffices r ^ 2 - algebraMap _ _ a = 0 by grind
  simpa using h.aeval_gen

variable [Nontrivial R]

include h in
theorem nontrivial : Nontrivial S :=
  h.toIsIntegralUnique.nontrivial (by apply_fun natDegree; simp)

include h in
theorem finrank : Module.finrank R S = 2 := by simpa using h.finrank_eq_natDegree

include h in
theorem isQuadraticExtension :
    Algebra.IsQuadraticExtension R S where
  __ := h.free
  finrank_eq_two' := h.finrank

noncomputable def basis : Module.Basis (Fin 2) R S :=
  h.toIsIntegralUniqueGen.basis.reindex (finCongr (by simp))

theorem basis_0 : h.basis 0 = 1 := by simp [basis]

theorem basis_1 : h.basis 1 = r := by simp [basis]

noncomputable def coeff := h.toIsIntegralUniqueGen.coeff

theorem basis_repr_eq_coeff (y : S) (i : Fin 2) :
    h.basis.repr y i = h.coeff y ↑i :=
  h.toIsIntegralUniqueGen.basis_repr_eq_coeff y (finCongr (by simp) i)

theorem coeff_apply_of_two_le (z : S) {i : ℕ} (hi : 2 ≤ i) :
    h.coeff z i = 0 :=
  h.toIsIntegralUniqueGen.coeff_apply_of_natDegree_le z (by simpa using hi)

@[simp]
theorem coeff_one : h.coeff 1 = Pi.single 0 1 :=
  letI _ := h.nontrivial
  h.toIsIntegralUniqueGen.coeff_one

@[simp]
theorem coeff_root : h.coeff r = Pi.single 1 1 :=
  h.toIsIntegralUniqueGen.coeff_root (by simp)

@[simp]
theorem coeff_algebraMap (k : R) : h.coeff (algebraMap _ _ k) = Pi.single 0 k :=
  letI _ := h.nontrivial
  h.toIsIntegralUniqueGen.coeff_algebraMap k

@[simp]
theorem coeff_ofNat (n : ℕ) [Nat.AtLeastTwo n] : h.coeff ofNat(n) = Pi.single 0 (n : R) :=
  letI _ := h.nontrivial
  h.toIsIntegralUniqueGen.coeff_ofNat n

theorem ext_elem ⦃y z : S⦄ (hyz : ∀ i < 2, h.coeff y i = h.coeff z i) :
    y = z :=
  h.toIsIntegralUniqueGen.ext_elem (by simpa using hyz)

theorem ext_elem_iff {y z : S} :
    y = z ↔ ∀ i < 2, h.coeff y i = h.coeff z i := by
  simpa using h.toIsIntegralUniqueGen.ext_elem_iff

theorem self_eq_coeff (x : S) :
    x = algebraMap _ _ (h.coeff x 0) + algebraMap _ _ (h.coeff x 1) * r := by
  rw [h.ext_elem_iff]
  intro i hi
  interval_cases i <;> simp [← Algebra.smul_def]

theorem coeff_of_add_of_mul_root {x y : R} :
    h.coeff (algebraMap _ _ x + algebraMap _ _ y * r) = fun₀ | 0 => x | 1 => y := by
  ext i
  by_cases! hi : i < 2
  · interval_cases i <;> simp [← Algebra.smul_def]
  · grind [h.coeff_apply_of_two_le]

end Ring

section CommRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Nontrivial R]
         {r : S} {a : R} (h : IsIntegralGenSqrt r a)

@[simp]
theorem coeff_mul (x y) :
    h.coeff (x * y) =
    fun₀
    | 0 => h.coeff x 0 * h.coeff y 0 + a * h.coeff x 1 * h.coeff y 1
    | 1 => h.coeff x 0 * h.coeff y 1 + h.coeff y 0 * h.coeff x 1 := by
  nth_rw 1 [h.self_eq_coeff x, h.self_eq_coeff y]
  rw [← coeff_of_add_of_mul_root h]
  congr
  ring_nf
  simp only [h.sq_root, map_add, map_mul]
  ring

@[simp]
theorem coeff_pow_two (x) :
    h.coeff (x ^ 2) =
    fun₀
    | 0 => h.coeff x 0 ^ 2 + a * h.coeff x 1 ^ 2
    | 1 => 2 * h.coeff x 0 * h.coeff x 1 := by
  rw [pow_two]
  ext i
  by_cases! hi : i < 2
  · interval_cases i <;> simp <;> ring
  · simp [show i ≠ 0 ∧ i ≠ 1 by omega]

end CommRing

section Field

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
         {r : L} {a : K} (h : IsIntegralGenSqrt r a)

include h in
theorem not_isSquare : ¬ IsSquare a := by
  simpa [X_sq_sub_C_irreducible_iff_not_isSquare] using h.irreducible_gen

include h in
theorem ne_zero : a ≠ 0 := fun hc ↦ not_isSquare h (by aesop)

end Field

end IsIntegralGenSqrt

section Field

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {r : L} {a : K}

theorem IsIntegralUnique.of_sqrt {a : K} (ha : ¬ IsSquare a)
    {r : L} (h : r ^ 2 = algebraMap _ _ a) : IsIntegralUnique r (X ^ 2 - C a) := by
  have root : (X ^ 2 - C a).aeval r = 0 := by simp [h]
  have monic : (X ^ 2 - C a).Monic := by simp [Monic]
  convert IsIntegrallyClosed.isIntegralUnique ⟨_, monic, root⟩
  rw [← X_sq_sub_C_irreducible_iff_not_isSquare] at ha
  exact minpoly.eq_of_irreducible_of_monic ha root monic

theorem IsQuadraticExtension.isGenerator_of_notMem_bot [Algebra.IsQuadraticExtension K L]
    (h : r ∉ (⊥ : Subalgebra K L)) : IsGenerator K r where
  adjoin_eq_top := by
    have : adjoin K {r} ≠ ⊥ := fun hc ↦ h (by simp [← hc])
    have := (Subalgebra.isSimpleOrder_of_finrank_prime K L
      (by simpa [Algebra.IsQuadraticExtension.finrank_eq_two] using Nat.prime_two)).eq_bot_or_eq_top
        (adjoin K {r})
    grind
    -- TODO : fix proof

theorem IsIntegralGenSqrt.of_sqrt [Algebra.IsQuadraticExtension K L]
    (h₁ : r ∉ (⊥ : Subalgebra K L)) (h₂ : r ^ 2 = algebraMap _ _ a) : IsIntegralGenSqrt r a where
  __ : IsIntegralUnique .. := by
    refine .of_sqrt (fun ⟨r', h'⟩ ↦ ?_) h₂
    apply_fun algebraMap _ L at h'
    rw [h', map_mul, ← pow_two] at h₂
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ h₂ with (h | h) <;> simp_all
  __ := IsQuadraticExtension.isGenerator_of_notMem_bot h₁

variable (L) in
theorem Algebra.IsQuadraticExtension.exists_isAdjoinRootMonic_X_pow_two_sub_C
    [Algebra.IsQuadraticExtension K L] (hK : ringChar K ≠ 2) :
    ∃ a : K, IsAdjoinRootMonic' L (X ^ 2 - C a) := by
  have : (⊥ : Subalgebra K L) ≠ ⊤ := by
    simp [Subalgebra.bot_eq_top_iff_finrank_eq_one, Algebra.IsQuadraticExtension.finrank_eq_two]
  rcases SetLike.exists_not_mem_of_ne_top ⊥ this rfl with ⟨s, hs⟩
  have h : IsIntegralUniqueGen s _ := {
    IsIntegrallyClosed.isIntegralUnique (Algebra.IsIntegral.isIntegral (R := K) s),
    IsQuadraticExtension.isGenerator_of_notMem_bot hs with }
  have sdeg : (minpoly K s).natDegree = 2 := by
    rw [← h.finrank_eq_natDegree, Algebra.IsQuadraticExtension.finrank_eq_two]
  use ((h.coeff (s ^ 2) 1) ^ 2 + 4 * h.coeff (s ^ 2) 0)
  refine .ofIsIntegralUniqueGen (x := 2 * s - algebraMap _ _ (h.coeff (s ^ 2) 1))
    (IsIntegralGenSqrt.of_sqrt (fun hc ↦ hs ?_) ?_).toIsIntegralUniqueGen
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

theorem IsIntegralGenSqrt.isSquare_div {r₁ r₂ : L} {a₁ a₂ : K} (hK : ringChar K ≠ 2)
    (h₁ : IsIntegralGenSqrt r₁ a₁) (h₂ : IsIntegralGenSqrt r₂ a₂) : IsSquare (a₁ / a₂) := by
  have a₂_ne_zero : a₂ ≠ 0 := h₂.ne_zero
  have eq : r₂ ^ 2 = algebraMap _ _ a₂ := h₂.sq_root
  rw [h₁.ext_elem_iff] at eq
  have := eq 0
  rcases show h₁.coeff r₂ 0 = 0 ∨ h₁.coeff r₂ 1 = 0 by simpa [Ring.two_ne_zero hK] using eq 1
  with (h0 | h1)
  · use (h₁.coeff r₂ 1)⁻¹
    have : h₁.coeff r₂ 1 ≠ 0 := fun hc ↦ a₂_ne_zero (by simp_all)
    field_simp
    simp_all
  · absurd h₂.not_isSquare
    exact ⟨h₁.coeff r₂ 0, by simp_all [pow_two]⟩

theorem IsAdjoinRootMonic'.isSquare_div {a₁ a₂ : K} (hK : ringChar K ≠ 2)
    (h₁ : IsAdjoinRootMonic' L (X ^ 2 - C a₁)) (h₂ : IsAdjoinRootMonic' L (X ^ 2 - C a₂)) :
    IsSquare (a₁ / a₂) := IsIntegralGenSqrt.isSquare_div hK ⟨h₁.pe⟩ ⟨h₂.pe⟩

theorem IsAdjoinRootMonic'.of_isIntegralGenSqrt_of_isSquare_div {r₁ : L} {a₁ a₂ : K} (ha₂ : a₂ ≠ 0)
    (ha : IsSquare (a₁ / a₂)) (h : IsIntegralGenSqrt r₁ a₁) :
    IsAdjoinRootMonic' L (X ^ 2 - C a₂) where
  exists_root := by
    rcases ha with ⟨m, hm⟩
    field_simp at hm
    have mz : m ≠ 0 := fun hc ↦ h.ne_zero (by simp_all)
    use (algebraMap _ _ m⁻¹) * r₁
    refine { IsIntegralUnique.of_sqrt (fun hc ↦ h.not_isSquare (by aesop)) ?_,
            h.algberaMap_mul (inv_ne_zero mz) with }
    calc
      (algebraMap _ _ m⁻¹ * r₁) ^ 2 = algebraMap _ _ m⁻¹ ^ 2 * r₁ ^ 2 := by ring
      _ = algebraMap _ _ (m⁻¹ ^ 2 * a₁) := by simp [h.sq_root]
      _ = algebraMap _ _ a₂ := by rw [hm]; field_simp
  f_monic := by simp [Monic]

theorem IsAdjoinRootMonic'.of_isAdjoinRootMonic_of_isSquare_div {a₁ a₂ : K} (ha₂ : a₂ ≠ 0)
    (ha : IsSquare (a₁ / a₂)) (h : IsAdjoinRootMonic' L (X ^ 2 - C a₁)) :
    IsAdjoinRootMonic' L (X ^ 2 - C a₂) :=
  .of_isIntegralGenSqrt_of_isSquare_div ha₂ ha ⟨h.pe⟩

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
    ⟦.mk0 (Classical.choose (Algebra.IsQuadraticExtension.exists_isAdjoinRootMonic_X_pow_two_sub_C L hK))
      (IsIntegralGenSqrt.ne_zero ⟨(Classical.choose_spec (Algebra.IsQuadraticExtension.exists_isAdjoinRootMonic_X_pow_two_sub_C L hK)).pe⟩)⟧
  left_inv := sorry
  right_inv := sorry

end Field
