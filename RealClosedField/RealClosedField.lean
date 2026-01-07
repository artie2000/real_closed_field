/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.OrderedAlgebra
import RealClosedField.Algebra.Order.Field.IsSemireal
import Mathlib.Algebra.Polynomial.SpecificDegree

-- TODO : figure out simp-normal form issue
attribute [simp] IsSquare.sq

open Polynomial

/-- A field `R` is real closed if
    1. `R` is real
    2. for all `x ∈ R`, either `x` or `-x` is a square
    3. every odd-degree polynomial has a root.
-/
class IsRealClosed (R : Type*) [Field R] : Prop extends IsSemireal R where
  isSquare_or_isSquare_neg (x : R) : IsSquare x ∨ IsSquare (-x)
  exists_isRoot_of_odd_natDegree {f : R[X]} (hf : Odd f.natDegree) : ∃ x, f.IsRoot x

attribute [aesop 90% forward] IsRealClosed.isSquare_or_isSquare_neg

/-- A real closure of an ordered field is a real closed ordered algebraic extension. -/
class IsRealClosure (K R : Type*) [Field K] [Field R] [LinearOrder K] [LinearOrder R] [Algebra K R]
    [IsStrictOrderedRing R] [IsStrictOrderedRing K] extends
    IsRealClosed R, IsOrderedModule K R, Algebra.IsAlgebraic K R

namespace IsRealClosed

universe u

variable {R : Type u} [Field R]

/-! # Sufficient conditions to be real closed -/

theorem mk' [IsSemireal R]
    (isSquare_of_not_isSquare_neg : ∀ {x : R}, ¬ IsSquare (-x) → IsSquare x)
    (exists_isRoot_of_odd_natDegree :
      ∀ {f : R[X]}, 1 < f.natDegree → Odd f.natDegree → ∃ x, f.IsRoot x) :
    IsRealClosed R where
  isSquare_or_isSquare_neg := by grind
  exists_isRoot_of_odd_natDegree {f} hodd := by
    by_cases hf : f.natDegree = 1
    · exact?

-- TODO : idiomatic way to say a disjunction is saturated?
theorem of_isAdjoinRoot_i_or_finrank_eq_one
    (hR : ¬ IsSquare (-1 : R))
    (h : ∀ K : Type u, [Field K] → [Algebra R K] → [FiniteDimensional R K] →
       IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X]) ∨ Module.finrank R K = 1) :
    IsRealClosed R := by
  have finrank_le (K : Type u) [Field K] [Algebra R K] [FiniteDimensional R K] :
      Module.finrank R K ≤ 2 := by
    rcases h K with (hK | hK)
    · simp [hK.finrank_eq_natDegree]
    · simp [hK]
  have : Fact (Irreducible (X ^ 2 + 1 : R[X])) := Fact.mk <| by
    simpa [← X_sq_sub_C_irreducible_iff_not_isSquare] using hR
  have := AdjoinRoot.finite (f := (X ^ 2 + 1 : R[X])) (by simp [Monic])
  have hK := AdjoinRoot.isAdjoinRootMonic' (f := (X ^ 2 + 1 : R[X])) (by simp [Monic])
  have hK₂ : ∀ x : AdjoinRoot (X ^ 2 + 1 : R[X]), IsSquare x := fun x ↦ by
    by_contra hi
    rw [← X_sq_sub_C_irreducible_iff_not_isSquare] at hi
    have := Fact.mk hi
    have := AdjoinRoot.finite (f := X ^ 2 - C x) (by simp [Monic])
    let : Module R (AdjoinRoot (X ^ 2 - C x)) := inferInstance -- TODO : remove this shortcut instance
    let := Module.Finite.trans
      (R := R) (AdjoinRoot (X ^ 2 + 1 : R[X])) (AdjoinRoot (X ^ 2 - C x))
    have fk_mul := Module.finrank_mul_finrank
      R (AdjoinRoot (X ^ 2 + 1 : R[X])) (AdjoinRoot (X ^ 2 - C x))
    have := finrank_le (AdjoinRoot (X ^ 2 - C x))
    simp [← fk_mul, Monic] at this
  refine { (?_ : IsSemireal R) with
            isSquare_or_isSquare_neg x := ?_,
            exists_isRoot_of_odd_natDegree {f} hf := ?_ }
  · exact .of_forall_adjoinRoot_i_isSquare hK hK₂
  · suffices (¬ IsSquare x → IsSquare (-x)) by tauto
    intro hx
    have iu : IsIntegralGenSqrt (AdjoinRoot.root (X ^ 2 - C x)) x :=
      ⟨AdjoinRoot.isIntegralUniqueGen (by simp [Monic])⟩
    have := iu.finite
    have : Fact (Irreducible (X ^ 2 - C x)) := Fact.mk <| by
      simpa [← X_sq_sub_C_irreducible_iff_not_isSquare] using hx
    rcases h (AdjoinRoot (X ^ 2 - C x)) with (ar' | fr)
    · have iu' : IsIntegralGenSqrt ar'.root (-1 : R) := ⟨by simpa using ar'.pe⟩
      have cl := calc
        iu.coeff ar'.root 0 ^ 2 + x * iu.coeff ar'.root 1 ^ 2 =
        iu.coeff (ar'.root ^ 2) 0 := by simp
        _ = -1 := by simp [iu'.sq_root]
      have : iu.coeff ar'.root 1 ≠ 0 := fun hc ↦ hR (by simp [← cl, hc])
      have : -x =
          (iu.coeff ar'.root 0 / iu.coeff ar'.root 1) ^ 2 + (1 / iu.coeff ar'.root 1) ^ 2 := by
        field_simp
        linear_combination - cl
      exact isSquare_of_isSumSq_of_forall_adjoinRoot_i_isSquare hK hK₂ (by aesop)
    · simp [iu.finrank] at fr
  · refine Polynomial.has_root_of_monic_odd_natDegree_imp_not_irreducible ?_ hf
    intro f hf_monic hf_odd hf_deg hf_irr
    have iu := AdjoinRoot.isIntegralUniqueGen hf_monic
    rw [← iu.finrank_eq_natDegree] at *
    have := Fact.mk hf_irr
    have := Module.finite_of_finrank_pos hf_odd.pos
    grind [finrank_le (AdjoinRoot f)]

theorem of_isAdjoinRoot_i_isAlgClosure {K : Type*} [Field K] [Algebra R K] [IsAlgClosure R K]
    (h : IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X])) : IsRealClosed R := by
  refine of_isAdjoinRoot_i_or_finrank_eq_one ?_ fun K _ _ _ ↦ ?_
  · simpa [← X_sq_sub_C_irreducible_iff_not_isSquare] using h.irreducible
  · rcases (IsAlgClosure.isAlgClosed R).nonempty_algEquiv_or_of_finrank_eq_two K
      (by simpa using h.finrank_eq_natDegree) with (hK | hK)
    · rw [Nonempty.congr AlgEquiv.symm AlgEquiv.symm,
          Module.nonempty_algEquiv_iff_finrank_eq_one] at hK
      exact Or.inr hK
    · exact Or.inl (h.map hK.some.symm)

theorem of_linearOrderedField [LinearOrder R] [IsStrictOrderedRing R]
    (isSquare_of_nonneg : ∀ {x : R}, 0 ≤ x → IsSquare x)
    (exists_isRoot_of_odd_natDegree : ∀ {f : R[X]}, Odd f.natDegree → ∃ x, f.IsRoot x) :
    IsRealClosed R where
  isSquare_or_isSquare_neg {x} := by
    rcases le_or_gt x 0 with (neg | pos)
    · exact Or.inr <| isSquare_of_nonneg (by linarith)
    · exact Or.inl <| isSquare_of_nonneg (by linarith)
  exists_isRoot_of_odd_natDegree := exists_isRoot_of_odd_natDegree

theorem of_intermediateValueProperty [LinearOrder R] [IsStrictOrderedRing R]
    (h : ∀ {f : R[X]} {x y : R}, x ≤ y → 0 ≤ f.eval x → f.eval y ≤ 0 →
       ∃ z ∈ Set.Icc x y, f.eval z = 0) :
    IsRealClosed R := by
  refine .of_linearOrderedField (fun {x} hx ↦ ?_) (fun {f} hf ↦ ?_)
  · have : x ≤ (x + 1) ^ 2 := by
      suffices 0 ≤ 1 + x + x ^ 2 by linear_combination this
      positivity
    rcases h (f := - X ^ 2 + C x) (x := 0) (y := x + 1)
      (by linarith) (by simpa using hx) (by simpa using this) with ⟨z, _, hz⟩
    exact ⟨z, by linear_combination (by simpa using hz : _ = (0 : R))⟩
  · rcases sign_change hf with ⟨x, y, hx, hy⟩
    wlog hxy : y ≤ x
    · simpa using this h (f := -f) (by simpa using hf) y x
        (by simpa using hy) (by simpa using hx) (by order)
    rcases h hxy (by order) (by order) with ⟨z, _, hz⟩
    exact ⟨z, hz⟩

theorem of_maximal_isOrderedAlgebra [LinearOrder R] [IsStrictOrderedRing R]
    (h : ∀ K : Type u, [Field K] → [LinearOrder K] → [IsStrictOrderedRing K] → [Algebra R K] →
           [Algebra.IsAlgebraic R K] → [IsOrderedModule R K] → Module.finrank R K = 1) :
    IsRealClosed R := by
  refine .of_linearOrderedField (fun {x} hx ↦ ?_) (fun {f} hf ↦ ?_)
  · by_contra hx₂
    have ar := AdjoinRoot.isAdjoinRootMonic' (f := X ^ 2 - C x) (by simp [Monic])
    have := ar.finite
    have : Fact (Irreducible (X ^ 2 - C x)) := Fact.mk <| by
      simpa [← X_sq_sub_C_irreducible_iff_not_isSquare] using hx₂
    rcases adj_sqrt_ordered hx hx₂ with ⟨_, _, _⟩
    have := h (AdjoinRoot (X ^ 2 - C x))
    simp [ar.finrank_eq_natDegree] at this
  · refine Polynomial.has_root_of_monic_odd_natDegree_imp_not_irreducible ?_ hf
    intro f hf_monic hf_odd hf_deg hf_irr
    have ar := AdjoinRoot.isAdjoinRootMonic' hf_monic
    rw [← ar.finrank_eq_natDegree] at *
    have := ar.finite
    have := Fact.mk hf_irr
    rcases odd_deg_ordered hf_odd with ⟨_, _, _⟩
    exact hf_deg (h (AdjoinRoot f))

theorem of_maximal_isSemireal [IsSemireal R]
    (h : ∀ K : Type u, [Field K] → [IsSemireal K] → [Algebra R K] → [Algebra.IsAlgebraic R K] →
         Module.finrank R K = 1) :
    IsRealClosed R :=
  let := LinearOrder.ofIsSemireal R
  .of_maximal_isOrderedAlgebra fun K ↦ by exact h K

section IsRealClosed

variable [IsRealClosed R]

-- TODO : proper sqrt operation + API?

@[aesop 50%]
theorem _root_.IsSquare.of_not_isSquare_neg {x : R} (hx : ¬ IsSquare (-x)) : IsSquare x := by aesop

theorem _root_.IsSquare.of_isSumSq {x : R} (hx : IsSumSq x) : IsSquare x := by
  suffices IsSquare (-x) → x = 0 by aesop
  exact (IsFormallyReal.eq_zero_of_isSumSq_of_neg_isSumSq hx <| IsSquare.isSumSq ·)

instance : Fact (Irreducible (X ^ 2 + 1 : R[X])) := Fact.mk <| by
  suffices ¬ IsSquare (-1 : R) by
    simpa [← Polynomial.X_sq_sub_C_irreducible_iff_not_isSquare] using this
  aesop (add safe forward IsSemireal.not_isSumSq_neg_one)

theorem exists_eq_pow_of_odd (x : R) {n : ℕ} (hn : Odd n) : ∃ r, x = r ^ n := by
  rcases exists_isRoot_of_odd_natDegree (f := X ^ n - C x) (by simp [hn]) with ⟨r, hr⟩
  exact ⟨r, by linear_combination - (by simpa using hr : r ^ n - x = 0)⟩

theorem exists_eq_pow_of_isSquare {x : R} (hx : IsSquare x) {n : ℕ} (hn : n > 0) :
    ∃ r, x = r ^ n := by
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    rcases Nat.even_or_odd n with (even | odd)
    · rcases even with ⟨m, hm⟩
      rcases hx with ⟨s, hs⟩
      rcases isSquare_or_isSquare_neg s with (h | h) <;>
        rcases ih m (by omega) h (by omega) with ⟨r, hr⟩ <;>
        exact ⟨r, by simp [hm, pow_add, ← hr, hs]⟩
    · exact exists_eq_pow_of_odd x odd

/-! # Classification of algebraic extensions of a real closed field -/

section ext

variable (R) {K : Type*} [Field K] [Algebra R K]

theorem odd_finrank_extension [FiniteDimensional R K] (hK :  Odd (Module.finrank R K)) :
    Module.finrank R K = 1 := by
  rcases Field.exists_isAdjoinRootMonic R K with ⟨f, hf⟩
  rw [hf.finrank_eq_natDegree] at *
  rcases exists_isRoot_of_odd_natDegree (f := f) hK with ⟨x, hx⟩
  simpa using natDegree_eq_of_degree_eq_some <|
    degree_eq_one_of_irreducible_of_root hf.irreducible hx

variable (K) in
theorem isAdjoinRoot_i_of_isQuadraticExtension [Algebra.IsQuadraticExtension R K] :
    IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X]) := by
  rcases Algebra.IsQuadraticExtension.exists_isAdjoinRootMonic_X_pow_two_sub_C K (K := R) (by simp)
    with ⟨a, hK⟩
  have iu : IsIntegralGenSqrt _ a := ⟨hK.pe⟩
  simpa using IsAdjoinRootMonic'.of_isAdjoinRootMonic_of_isSquare_div (a₂ := -1)
    (by simp) (by field_simp; aesop (add safe forward iu.not_isSquare)) hK

theorem isSquare_algebraMap_of_isAdjoinRoot_i (hK : IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X]))
    (x : R) : IsSquare (algebraMap _ K x) := by
  let i := hK.root -- prevents the `X ^ 2 + 1` argument being rewritten
  have iu : IsIntegralGenSqrt i (-1 : R) := ⟨by simpa using hK.pe⟩
  rcases isSquare_or_isSquare_neg x with (pos | neg)
  · rcases pos with ⟨r, rfl⟩
    exact ⟨algebraMap _ _ r, by simp⟩
  · rcases neg with ⟨r, hr⟩
    use i * algebraMap _ _ r
    apply_fun algebraMap R K at hr
    simp only [map_neg, map_mul] at hr
    ring_nf at hr ⊢
    simp [← hr, iu.sq_root]

theorem isSquare_of_isAdjoinRoot_i (hK : IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X]))
    (x : K) : IsSquare x := by
  let i := hK.root -- prevents the `X ^ 2 + 1` argument being rewritten
  have hRi : IsIntegralGenSqrt i (-1 : R) := ⟨by simpa using hK.pe⟩
  rw [hRi.self_eq_coeff x]
  rcases eq_or_ne (hRi.coeff x 1) 0 with (zero | ne)
  · rw [zero]
    suffices IsSquare (algebraMap _ _ (hRi.coeff x 0)) by aesop
    exact isSquare_algebraMap_of_isAdjoinRoot_i R hK _
  · rcases isSquare_of_isSumSq (x := (hRi.coeff x 0) ^ 2 + (hRi.coeff x 1) ^ 2) (by aesop)
      with ⟨r₁, hr₁⟩
    apply_fun algebraMap R K at hr₁
    simp only [map_add, map_pow, ← pow_two] at hr₁
    rcases isSquare_algebraMap_of_isAdjoinRoot_i R hK (((hRi.coeff x 0) + r₁) / 2)
      with ⟨r₂, hr₂⟩
    simp only [map_div₀, map_add, map_ofNat, ← pow_two] at hr₂
    have : (2 : K) ≠ 0 := by
      -- TODO : add lemma about `CharZero` being preserved by algebra extensions
      have : CharZero K := by
        simp [← Algebra.ringChar_eq R, ← CharP.ringChar_zero_iff_CharZero]
      exact two_ne_zero
    have : r₂ ≠ 0 := fun hc ↦ by
      have : (algebraMap R K) (hRi.coeff x 0) = - (algebraMap R K) r₁ := by
        linear_combination
          (by simp_all : (algebraMap R K) (hRi.coeff x 0) + (algebraMap R K) r₁ = 0)
      rw [this] at hr₁
      exact ne <| (algebraMap.coe_inj _ _).mp <| by -- TODO : add more usable inj lemmas
        simpa using eq_zero_of_pow_eq_zero (a := algebraMap _ K (hRi.coeff x 1)) (n := 2)
          (by linear_combination hr₁)
    use r₂ + algebraMap _ _ (hRi.coeff x 1) / (2 * r₂) * i
    field_simp
    rw [← hr₂]
    field_simp
    ring_nf
    simp only [hRi.sq_root, map_neg, map_one]
    rw [← hr₁]
    ring

theorem finrank_neq_two_of_isAdjoinRoot_i (hK : IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X]))
    (L : Type*) [Field L] [Algebra K L] :
    Module.finrank K L ≠ 2 := fun hL ↦ by
  have : Algebra.IsQuadraticExtension K L := ⟨hL⟩
  rcases Algebra.IsQuadraticExtension.exists_isAdjoinRootMonic_X_pow_two_sub_C L
    (K := K) (by simp [← Algebra.ringChar_eq R]) with ⟨x, hL⟩
  absurd (show ¬ IsSquare x by
      simpa [Polynomial.X_sq_sub_C_irreducible_iff_not_isSquare] using hL.irreducible)
  exact isSquare_of_isAdjoinRoot_i R hK x

variable (K) in
theorem finite_extension_rank_le [FiniteDimensional R K] : Module.finrank R K ≤ 2 := by
  wlog hGal : IsGalois R K generalizing K
  · have := this (IntermediateField.normalClosure R K (AlgebraicClosure K)) inferInstance
    have := Module.finrank_bot_le_finrank_of_isScalarTower
      R K (IntermediateField.normalClosure R K (AlgebraicClosure K))
    have := Module.finrank_pos (R := R) (M := K)
    omega
  rcases Nat.exists_eq_two_pow_mul_odd (n := Module.finrank R K) Module.finrank_pos.ne'
    with ⟨k, a, ha, hka⟩
  have a_val : a = 1 := by
    rcases IsGalois.exists_intermediateField_of_card_pow_prime_mul
      Nat.prime_two hka (by simp : 0 ≤ k) with ⟨M, hM⟩
    simp_all [odd_finrank_extension R (K := M) (by grind)]
  suffices k ≤ 1 by interval_cases k <;> simp_all
  by_contra! k_ge
  rcases IsGalois.exists_intermediateField_of_card_pow_prime_mul
    Nat.prime_two hka (by omega : 1 ≤ k) with ⟨M, hM⟩
  rcases IsGalois.exists_intermediateField_ge_card_pow_prime_mul_of_card_pow_prime_mul
    Nat.prime_two hka hM (by omega : 1 ≤ 2) (by omega) with ⟨N, hN_ge, hN⟩
  rw [ge_iff_le] at hN_ge
  have : Algebra.IsQuadraticExtension R M := ⟨by omega⟩
  algebraize [(IntermediateField.inclusion hN_ge).toRingHom]
  have := IsScalarTower.of_algebraMap_eq'
    (IntermediateField.inclusion hN_ge).comp_algebraMap.symm
  have := Module.Finite.of_restrictScalars_finite R M N
  apply finrank_neq_two_of_isAdjoinRoot_i R (isAdjoinRoot_i_of_isQuadraticExtension R M) N
  rw [Module.finrank_dvd_finrank' R M N, hM, hN]
  simp_all

theorem rank_eq_one_of_isAdjoinRoot_i (hK : IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X])) (L : Type*)
    [Field L] [Algebra R L] [Algebra K L] [FiniteDimensional R L] [IsScalarTower R K L] :
    Module.finrank K L = 1 := by
  have : Module.finrank R K = 2 := by simp [hK.finrank_eq_natDegree]
  grind [Module.finrank_mul_finrank R K L,
         Module.finrank_pos (R := R) (M := L), finite_extension_rank_le R L]

variable (K) in
theorem finite_extension_classify [FiniteDimensional R K] :
    IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X]) ∨ Module.finrank R K = 1 := by
  have := finite_extension_rank_le R K
  interval_cases h : Module.finrank R K
  · simp [Module.finrank_pos.ne'] at h
  · simp
  · have : Algebra.IsQuadraticExtension R K := ⟨h⟩
    exact Or.inl <| isAdjoinRoot_i_of_isQuadraticExtension R K

variable (K) in
instance [Algebra.IsAlgebraic R K] : FiniteDimensional R K := by
  by_contra hK
  rcases IntermediateField.exists_lt_finrank_of_infinite_dimensional hK 2 with ⟨M, _, hM⟩
  rcases finite_extension_classify R M with (sq | triv)
  · simp_all [sq.finrank_eq_natDegree]
  · simp_all

variable (K) in
theorem maximal_isSemireal [IsSemireal K] [Algebra.IsAlgebraic R K] : Module.finrank R K = 1 := by
  rcases finite_extension_classify R K with (sq | triv)
  · have iu : IsIntegralGenSqrt sq.root (-1 : R) := ⟨by simpa using sq.pe⟩
    absurd (show ¬ IsSquare (-1 : K) from
      fun hc ↦ IsSemireal.not_isSumSq_neg_one K (IsSquare.isSumSq hc))
    exact ⟨sq.root, by simpa [pow_two] using iu.sq_root.symm⟩
  · exact triv

variable (K) in
theorem isAdjoinRoot_i_of_isAlgClosure [IsAlgClosure R K] :
    IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X]) := by
  rcases finite_extension_classify R K with (sq | triv)
  · exact sq
  · rw [← Module.nonempty_algEquiv_iff_finrank_eq_one] at triv
    have := IsSquare.map triv.some.symm ((IsAlgClosure.isAlgClosed R).isSquare (-1 : K))
    aesop (add safe forward IsSemireal.not_isSumSq_neg_one)

instance [IsAlgClosure R K] : Algebra.IsQuadraticExtension R K :=
  IsIntegralGenSqrt.isQuadraticExtension (a := -1)
    ⟨by simpa using (isAdjoinRoot_i_of_isAlgClosure R K).pe⟩

variable {R} in
theorem isAlgClosure_iff_isAdjoinRoot_i :
    IsAlgClosure R K ↔ IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X]) where
  mp h := isAdjoinRoot_i_of_isAlgClosure R K
  mpr h := {
    isAlgClosed := .of_finiteDimensional_imp_finrank_eq_one K fun L _ _ _ ↦ by
      have := h.finite
      algebraize [(algebraMap K L).comp (algebraMap R K)]
      have := Module.Finite.trans (R := R) K L
      exact rank_eq_one_of_isAdjoinRoot_i R h L
    isAlgebraic := have := h.finite; inferInstance
  }

theorem isAlgClosure_of_isAdjoinRoot_i (hK : IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X])) :
    IsAlgClosure R K := isAlgClosure_iff_isAdjoinRoot_i.mpr hK

theorem isAlgClosure_of_finrank_ne_one [Algebra.IsAlgebraic R K] (hK : Module.finrank R K ≠ 1) :
    IsAlgClosure R K := by
  rcases finite_extension_classify R K with (sq | triv)
  · exact isAlgClosure_of_isAdjoinRoot_i R sq
  · contradiction

end ext

theorem irred_poly_classify {f : R[X]} (hf : f.Monic) :
    Irreducible f ↔ f.natDegree = 1 ∨ (∃ a b : R, b ≠ 0 ∧ f = (X - C a) ^ 2 + C b ^ 2) where
  mp h := by
    have := Fact.mk h
    have := hf.finite_adjoinRoot
    have finrk : Module.finrank R (AdjoinRoot f) = f.natDegree := by simpa using
      (AdjoinRoot.powerBasis hf.ne_zero).finrank -- TODO : add this lemma in my notation
    rcases finite_extension_classify R (AdjoinRoot f) with (sq | triv)
    · apply Or.inr
      have iu : IsIntegralGenSqrt _ (-1 : R) := ⟨by simpa using sq.pe⟩
      set r := sq.root with hr
      have eq_root := iu.self_eq_coeff (AdjoinRoot.root f)
      refine ⟨iu.coeff (AdjoinRoot.root f) 0, iu.coeff (AdjoinRoot.root f) 1, fun hc ↦ ?_, ?_⟩
      · -- TODO : redo using `aeval`
        simp only [AdjoinRoot.algebraMap_eq, hc, map_zero, zero_mul, add_zero] at eq_root
        nth_rw 1 [← AdjoinRoot.mk_X, ← AdjoinRoot.mk_C, AdjoinRoot.mk_eq_mk] at eq_root
        have := Polynomial.natDegree_le_of_dvd eq_root (by apply_fun natDegree; simp)
        simp [iu.finrank, ← finrk] at this
      · suffices AdjoinRoot.mk f ((X - C (iu.coeff (AdjoinRoot.root f) 0)) ^ 2 +
                                 C (iu.coeff (AdjoinRoot.root f) 1) ^ 2) = 0 by
          rw [AdjoinRoot.mk_eq_zero] at this
          exact Polynomial.eq_of_dvd_of_natDegree_le_of_leadingCoeff this
            (by simp [iu.finrank, ← finrk]) (by simp [hf])
        simp [← AdjoinRoot.algebraMap_eq]
        nth_rw 1 [eq_root]
        ring_nf
        simp [iu.sq_root]
    · simp_all
  mpr h := by
    rcases h with (lin | quad)
    · exact Polynomial.irreducible_of_degree_eq_one
        (by simpa [Polynomial.natDegree_eq_one_iff_degree_eq_one] using lin)
    · rcases quad with ⟨a, b, hb, rfl⟩
      have h_deg : ((X - C a) ^ 2 + C b ^ 2).natDegree = 2 := by simp
      rw [hf.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega),
          Polynomial.roots_eq_zero_iff_isRoot_eq_bot hf.ne_zero]
      ext r
      suffices (r - a) ^ 2 + b ^ 2 ≠ 0 by simp [this]
      intro hc
      exact hb <| IsFormallyReal.eq_zero_of_mul_self <|
        IsFormallyReal.eq_zero_of_add_left (s₁ :=  (r - a) ^ 2) (by aesop) (by aesop) (by simpa [pow_two] using hc)

section LinearOrderedField

variable (R) in
noncomputable def unique_isStrictOrderedRing :
    Unique {l : LinearOrder R // IsStrictOrderedRing R} :=
  IsSemireal.unique_isStrictOrderedRing (by aesop)

variable [LinearOrder R] [IsStrictOrderedRing R]

theorem nonneg_iff_isSquare {x : R} : 0 ≤ x ↔ IsSquare x where
  mp h := by
    suffices IsSquare (-x) → x = 0 by aesop
    intro hc
    linarith [IsSquare.nonneg hc]
  mpr := IsSquare.nonneg

alias ⟨isSquare_of_nonneg, _⟩ := nonneg_iff_isSquare

theorem exists_eq_pow_of_nonneg {x : R} (hx : 0 ≤ x) {n : ℕ} (hn : n > 0) : ∃ r, x = r ^ n :=
  exists_eq_pow_of_isSquare (isSquare_of_nonneg hx) hn

theorem intermediate_value_property {f : R[X]} {x y : R}
    (hle : x ≤ y) (hx : 0 ≤ f.eval x) (hy : f.eval y ≤ 0) :
    ∃ z ∈ Set.Icc x y, f.eval z = 0 := by
  induction hdeg : f.natDegree using Nat.strong_induction_on generalizing f with
  | h n ih =>
    subst hdeg
    by_cases! hz : f.natDegree = 0
    · rw [f.eq_C_of_natDegree_eq_zero hz] at hx hy ⊢
      exact ⟨x, by simp_all; order⟩
    have hpos := Nat.pos_of_ne_zero hz
    by_cases! hdiv : ∃ g : R[X], g.natDegree > 0 ∧ g ∣ f ∧ 0 < g.eval y ∧ 0 < g.eval x
    · rcases hdiv with ⟨g, hg_deg, hg_div, hg_y, hg_x⟩
      rcases hg_div with ⟨k, rfl⟩
      rw [Polynomial.natDegree_mul
        (show g ≠ 0 from fun _ ↦ by simp_all) (show k ≠ 0 from fun _ ↦ by simp_all)] at ih
      rw [eval_mul] at hx hy
      rcases ih (k.natDegree) (by simp_all) (by nlinarith) (by nlinarith) rfl with ⟨z, hz_m, hz_e⟩
      refine ⟨z, hz_m, Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (by simp) hz_e⟩
    · rcases Polynomial.exists_monic_irreducible_factor f (f.not_isUnit_of_natDegree_pos hpos)
        with ⟨g, hg_m, hg_i, hg_d⟩
      rcases (irred_poly_classify hg_m).mp hg_i with (lin | quad)
      · rw [hg_m.eq_X_add_C lin] at hg_i hg_d hg_m
        by_cases! le_y : -g.coeff 0 < y
        · have := hdiv _ (by simp) hg_d
          simp only [eval_add, eval_C, eval_X] at this
          have := this (by linarith)
          use -g.coeff 0
          rw [Set.mem_Icc]
          exact ⟨⟨by linarith, by linarith⟩,
                Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hg_d (by simp)⟩
        · by_cases! y_le : y < -g.coeff 0
          · have := hdiv (-(X + C (g.coeff 0))) (by simp [↓Polynomial.natDegree_neg])
              (by simpa [↓neg_dvd] using hg_d)
            simp only [eval_add, eval_neg, eval_C, eval_X] at this
            linarith [this (by linarith)]
          · rw [show y = -g.coeff 0 by linarith] at hle ⊢
            exact ⟨-g.coeff 0, by simp [hle],
              Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hg_d (by simp)⟩
      · rcases quad with ⟨a, b, hb, g_eq⟩
        have pos : ∀ z, 0 < g.eval z := fun z ↦ by simp [g_eq]; positivity
        linarith [hdiv g hg_i.natDegree_pos hg_d (pos y), pos x]

end LinearOrderedField

end IsRealClosed

variable (R) in
theorem TFAE :
    [IsRealClosed R,
     IsAdjoinRootMonic' (AlgebraicClosure R) (X ^ 2 + 1 : R[X]),
     IsSemireal R ∧ (∀ K : Type u, [Field K] → [IsSemireal K] → [Algebra R K] →
                       [Algebra.IsAlgebraic R K] → Module.finrank R K = 1)].TFAE := by
  tfae_have 1 → 2 := fun _ ↦ isAdjoinRoot_i_of_isQuadraticExtension R (AlgebraicClosure R)
  tfae_have 1 → 3 := fun _ ↦ ⟨inferInstance, fun K ↦ maximal_isSemireal R K⟩
  tfae_have 2 → 1 := of_isAdjoinRoot_i_isAlgClosure
  tfae_have 3 → 1 := fun ⟨_, h⟩ ↦ of_maximal_isSemireal h
  tfae_finish

variable (R) in
theorem TFAE_linearOrderedField [LinearOrder R] [IsStrictOrderedRing R] :
    [IsRealClosed R,
    (∀ K : Type u, [Field K] → [LinearOrder K] → [IsStrictOrderedRing K] → [Algebra R K] →
      [Algebra.IsAlgebraic R K] → [IsOrderedModule R K] → Module.finrank R K = 1),
    (∀ {f : R[X]} {x y : R}, x ≤ y → 0 ≤ f.eval x → f.eval y ≤ 0 →
      ∃ z ∈ Set.Icc x y, f.eval z = 0)].TFAE := by
  tfae_have 1 → 2 := fun _ K ↦ maximal_isSemireal R K
  tfae_have 1 → 3 := fun _ ↦ intermediate_value_property
  tfae_have 2 → 1 := of_maximal_isOrderedAlgebra
  tfae_have 3 → 1 := of_intermediateValueProperty
  tfae_finish

end IsRealClosed

theorem weak_Artin_Schreier {R : Type*} [Field R] (hR_char : ringChar R ≠ 2)
    (hR : Module.finrank R (AlgebraicClosure R) = 2) : IsRealClosed R :=
  .of_isAdjoinRoot_i_isAlgClosure (K := AlgebraicClosure R) <| by
    sorry

theorem Artin_Schreier {R : Type*} [Field R]
    (hR : FiniteDimensional R (AlgebraicClosure R)) : IsRealClosed R :=
  sorry

namespace IsRealClosure

universe u v

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

-- TODO : "order extension" partial order on ordered subfields, to apply Zorn on

-- wrong def
/- variable (R) in
noncomputable def realClosure (K : Type v) [Field K] [Algebra R K] : IntermediateField R K :=
  Classical.choose <| zorn_le₀
    {L : IntermediateField R K | ∃ l : LinearOrder L, IsStrictOrderedRing L ∧ IsOrderedModule R L}
    fun c hc hc_chain ↦ by
  use sSup c
  refine ⟨?_, fun _ ↦ le_sSup⟩
  simp -/

end IsRealClosure
