/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.OrderedAlgebra
import RealClosedField.Algebra.Order.Field.Semireal

open Polynomial

/- An ordered field is real closed if every nonegative element is a square and
   every odd-degree polynomial has a root. -/
class IsRealClosed (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] : Prop where
  isSquare_of_nonneg {x : R} (hx : 0 ≤ x) : IsSquare x
  exists_isRoot_of_odd_natDegree {f : R[X]} (hf : Odd f.natDegree) : ∃ x, f.IsRoot x

-- TODO : figure out assumptions vs extends here
/- A real closure is a real closed ordered algebraic extension. -/
class IsRealClosure (K R : Type*) [Field K] [Field R] [LinearOrder K] [LinearOrder R] [Algebra K R]
    [IsStrictOrderedRing R] [IsStrictOrderedRing K] extends
    IsRealClosed R, IsOrderedModule K R, Algebra.IsAlgebraic K R

namespace IsRealClosed

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

section properties

variable [IsRealClosed R]

theorem isSquare_or_isSquare_neg (x : R) : IsSquare x ∨ IsSquare (-x) := by
  rcases lt_or_ge x 0 with (neg | pos)
  · exact Or.inr <| isSquare_of_nonneg (x := -x) (by linarith)
  · exact Or.inl <| isSquare_of_nonneg pos

noncomputable def unique_isStrictOrderedRing :
    Unique {l : LinearOrder R // @IsStrictOrderedRing R _ (l.toPartialOrder)} where
  default := ⟨inferInstance, inferInstance⟩
  uniq := by
    suffices ∃! l : LinearOrder R, @IsStrictOrderedRing R _ (l.toPartialOrder) from fun ⟨l, hl⟩ ↦
      Subtype.ext <| ExistsUnique.unique this hl inferInstance
    rw [IsStrictOrderedRing.unique_isStrictOrderedRing_iff]
    aesop (add unsafe isSquare_of_nonneg)

instance : Fact (Irreducible (X ^ 2 + 1 : R[X])) := Fact.mk <| by
  suffices ¬ IsSquare (-1 : R) by
    rw [← Polynomial.X_sq_sub_C_irreducible_iff_not_isSquare] at this
    simpa
  simp

-- TODO : proper sqrt operation + API?
set_option maxHeartbeats 2000000 in -- TODO : make the proof faster
theorem isSquare_adjoinRoot_i (x : AdjoinRoot (X ^ 2 + 1 : R[X])) : IsSquare x := by
  have hRi : IsIntegralGenSqrt _ (-1 : R) :=
    ⟨by simpa using AdjoinRoot.isIntegralUniqueGen (by simp [Monic])⟩
  rw [hRi.self_eq_coeff x]
  rcases eq_or_ne (hRi.coeff x 1) 0 with (zero | ne)
  · rw [zero]
    suffices IsSquare (algebraMap _ _ (hRi.coeff x 0)) by
      aesop (erase simp AdjoinRoot.algebraMap_eq)
    rcases isSquare_or_isSquare_neg (hRi.coeff x 0) with (pos | neg)
    · aesop
    · have : IsSquare (-1 : AdjoinRoot (X ^ 2 + 1 : R[X])) :=
        ⟨AdjoinRoot.root (X ^ 2 + 1), by simp [← pow_two, hRi.sq_root]⟩
      simpa using IsSquare.mul this (IsSquare.map (algebraMap _ _) neg)
  · rcases isSquare_of_nonneg (by positivity : 0 ≤ (hRi.coeff x 0) ^ 2 + (hRi.coeff x 1) ^ 2)
      with ⟨rt₁, hrt₁⟩
    have : - |rt₁| < (hRi.coeff x 0) :=
      (abs_lt_of_sq_lt_sq' (by simp [pow_two, ← hrt₁, ne]) (by simp)).1
    have : 0 < (hRi.coeff x 0) + |rt₁| := by linarith
    rcases isSquare_of_nonneg (by positivity : 0 ≤ ((hRi.coeff x 0) + |rt₁|) / 2)
      with ⟨rt₂, hrt₂⟩
    have : (algebraMap R (AdjoinRoot (X ^ 2 + 1 : R[X]))) |rt₂| ≠ 0 := fun hc ↦ by simp_all
    have : (2 : AdjoinRoot (X ^ 2 + 1 : R[X])) ≠ 0 := by
      -- TODO : add lemma about `CharZero` being preserved by algebra extensions
      have : CharZero (AdjoinRoot (X ^ 2 + 1 : R[X])) := by
        simp [← Algebra.ringChar_eq R, ← CharP.ringChar_zero_iff_CharZero]
      exact two_ne_zero
    use algebraMap _ _ |rt₂| + algebraMap _ _ (hRi.coeff x 1 / (2 * |rt₂|)) * AdjoinRoot.root (X ^ 2 + 1)
    simp [-AdjoinRoot.algebraMap_eq, map_ofNat]
    field_simp
    have : algebraMap R (AdjoinRoot (X ^ 2 + 1 : R[X])) |rt₂| ^ 2 =
           algebraMap _ _ ((hRi.coeff x 0 + |rt₁|) / 2) := by
      rw [← map_pow, sq_abs, pow_two rt₂, ← hrt₂]
    rw [this]
    simp [-AdjoinRoot.algebraMap_eq, map_ofNat]
    field_simp
    ring_nf
    simp [hRi.sq_root, -AdjoinRoot.algebraMap_eq]
    ring_nf
    have : algebraMap R (AdjoinRoot (X ^ 2 + 1 : R[X])) |rt₁| ^ 2 =
           algebraMap _ _ (hRi.coeff x 0 ^ 2 + hRi.coeff x 1 ^ 2) := by
      rw [← map_pow, sq_abs, pow_two rt₁, ← hrt₁]
    rw [this]
    simp [-AdjoinRoot.algebraMap_eq] -- times out
    ring -- times out

/-! # Classification of algebraic extensions of a real closed field -/

section ext

variable (R) {K : Type*} [Field K] [Algebra R K]

theorem even_finrank_extension [FiniteDimensional R K] (hK : Module.finrank R K ≠ 1) :
  Even (Module.finrank R K) := by
  by_contra hodd
  rcases Field.exists_isAdjoinRootMonic R K with ⟨f, hf⟩
  rw [hf.finrank_eq_natDegree] at *
  rcases exists_isRoot_of_odd_natDegree (f := f)
    (Nat.not_even_iff_odd.mp <| by simpa using hodd) with ⟨x, hx⟩
  exact hK <| by simpa using natDegree_eq_of_degree_eq_some <|
    degree_eq_one_of_irreducible_of_root hf.irreducible hx

variable (K) in
theorem isAdjoinRoot_i_of_isQuadraticExtension [Algebra.IsQuadraticExtension R K] :
    IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X]) := by
  rcases Algebra.IsQuadraticExtension.exists_isAdjoinRootMonic_X_pow_two_sub_C K (K := R) (by simp)
    with ⟨a, hK⟩
  have iu : IsIntegralGenSqrt _ a := ⟨hK.pe⟩
  rcases lt_or_ge 0 a with (pos | neg)
  · absurd (show ¬ IsSquare a by
      simpa [Polynomial.X_sq_sub_C_irreducible_iff_not_isSquare] using hK.irreducible)
    exact isSquare_of_nonneg pos.le
  · simpa using IsAdjoinRootMonic'.of_isAdjoinRootMonic_of_isSquare_div (a₂ := -1)
      (by simp) (isSquare_of_nonneg (by field_simp; linarith)) hK

theorem finrank_adjoinRoot_i_neq_two
    (L : Type*) [Field L] [Algebra (AdjoinRoot (X ^ 2 + 1 : R[X])) L] :
    Module.finrank (AdjoinRoot (X ^ 2 + 1 : R[X])) L ≠ 2 := fun hL ↦ by
  have : Algebra.IsQuadraticExtension (AdjoinRoot (X ^ 2 + 1)) L := ⟨hL⟩
  rcases Algebra.IsQuadraticExtension.exists_isAdjoinRootMonic_X_pow_two_sub_C L
    (K := AdjoinRoot (X ^ 2 + 1 : R[X])) (by simp [← Algebra.ringChar_eq R]) with ⟨x, hL⟩
  absurd (show ¬ IsSquare x by
      simpa [Polynomial.X_sq_sub_C_irreducible_iff_not_isSquare] using hL.irreducible)
  exact isSquare_adjoinRoot_i x

variable (K) in
theorem finite_extension_classify [FiniteDimensional R K] :
    IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X]) ∨ Module.finrank R K = 1 := by
  suffices 1 ≤ Module.finrank R K ∧ Module.finrank R K ≤ 2 by
    rcases this with ⟨_, _⟩
    interval_cases h : Module.finrank R K
    · simp
    · have : Algebra.IsQuadraticExtension R K := ⟨h⟩
      exact Or.inl <| isAdjoinRoot_i_of_isQuadraticExtension R K
  wlog hGal : IsGalois R K generalizing K
  · have := this ↥(IntermediateField.normalClosure R K (AlgebraicClosure K)) inferInstance
    have := Module.finrank_bot_le_finrank_of_isScalarTower
      R K ↥(IntermediateField.normalClosure R K (AlgebraicClosure K))
    have := Module.finrank_pos (R := R) (M := K)
    omega
  rcases Nat.exists_eq_two_pow_mul_odd (n := Module.finrank R K) Module.finrank_pos.ne'
    with ⟨k, a, ha, hka⟩

variable (K) in
theorem algebraic_extension_classify [Algebra.IsAlgebraic R K] :
    IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X]) ∨ Module.finrank R K = 1 := by sorry

variable (K) in
theorem maximal_isOrderedAlgebra [LinearOrder K] [IsOrderedRing K] [IsOrderedModule R K]
    [Algebra.IsAlgebraic R K] : Module.finrank R K = 1 := by
  rcases algebraic_extension_classify R K with (sq | triv)
  · sorry
  · exact triv

end ext

noncomputable def isAdjoinRoot_i_of_osAlgClosure
    {K : Type*} [Field K] [Algebra R K] [IsAlgClosure R K] :
    IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X]) := by sorry

theorem irred_poly_classify {f : R[X]} (hf : f.Monic) :
  Irreducible f ↔ f.natDegree = 1 ∨ (∃ a b : R, f = (X - C a) ^ 2 - C b ^ 2) := by sorry

theorem intermediate_value_property {f : R[X]} {x y : R}
    (hle : x ≤ y) (hx : 0 ≤ f.eval x) (hy : f.eval y ≤ 0) :
  ∃ z ∈ Set.Icc x y, f.eval z = 0 := by sorry

end properties

/-! # Sufficient conditions to be real closed -/

theorem of_isAdjoinRoot_i_or_finrank_eq_one
    (h : ∀ K : Type u, [Field K] → [Algebra R K] → [FiniteDimensional R K] →
       IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X]) ∨ Module.finrank R K = 1) :
    IsRealClosed R where
  isSquare_of_nonneg {x} hx := by
    by_contra hx₂
    have iu : IsIntegralGenSqrt (AdjoinRoot.root (X ^ 2 - C x)) x :=
      ⟨AdjoinRoot.isIntegralUniqueGen (by simp [Monic])⟩
    have := iu.finite
    have : Fact (Irreducible (X ^ 2 - C x)) := Fact.mk <| by
      simpa [← X_sq_sub_C_irreducible_iff_not_isSquare] using hx₂
    rcases h (AdjoinRoot (X ^ 2 - C x)) with (ar' | fr)
    · have iu' : IsIntegralGenSqrt ar'.root (-1 : R) := ⟨by simpa using ar'.pe⟩
      have := calc
        0 ≤ iu.coeff ar'.root 0 ^ 2 + x * iu.coeff ar'.root 1 ^ 2 := by positivity
        _ = iu.coeff (ar'.root ^ 2) 0 := by simp
        _ = -1 := by simp [iu'.sq_root]
      linarith
    · simp [iu.finrank] at fr
  exists_isRoot_of_odd_natDegree {f} hf := by
    refine Polynomial.has_root_of_monic_odd_natDegree_imp_not_irreducible ?_ hf
    intro f hf_monic hf_odd hf_deg hf_irr
    have iu := AdjoinRoot.isIntegralUniqueGen hf_monic
    rw [← (show _ = f.natDegree by simpa using iu.finrank_eq_natDegree)] at *
    have := Fact.mk hf_irr
    have := Module.finite_of_finrank_pos hf_odd.pos
    rcases h (AdjoinRoot f) with (ar' | fr)
    · simp [ar'.finrank_eq_natDegree] at hf_odd
      grind
    · exact hf_deg fr

theorem of_intermediateValueProperty
    (h : ∀ (f : R[X]) (x y : R), x ≤ y → 0 ≤ f.eval x → f.eval y ≤ 0 →
       ∃ z ∈ Set.Icc x y, f.eval z = 0) :
    IsRealClosed R where
  isSquare_of_nonneg {x} hx := by
    have : x ≤ (x + 1) ^ 2 := by
      suffices 0 ≤ 1 + x + x ^ 2 by linear_combination this
      positivity
    rcases h (- X ^ 2 + C x) 0 (x + 1) (by linarith) (by simpa using hx) (by simpa using this)
      with ⟨z, _, hz⟩
    exact ⟨z, by linear_combination (by simpa using hz : _ = (0 : R))⟩
  exists_isRoot_of_odd_natDegree {f} hf := by
    rcases sign_change hf with ⟨x, y, hx, hy⟩
    wlog hxy : y ≤ x
    · simpa using this h (f := -f) (by simpa using hf) y x
        (by simpa using hy) (by simpa using hx) (by order)
    rcases h f _ _ hxy (by order) (by order) with ⟨z, _, hz⟩
    exact ⟨z, hz⟩

theorem of_maximal_isOrderedAlgebra
    (h : ∀ K : Type u, [Field K] → [LinearOrder K] → [IsOrderedRing K] → [Algebra R K] →
           [FiniteDimensional R K] → [IsOrderedModule R K] → Module.finrank R K = 1) :
    IsRealClosed R where
  isSquare_of_nonneg {x} hx := by
    by_contra hx₂
    have ar := AdjoinRoot.isAdjoinRootMonic' (f := X ^ 2 - C x) (by simp [Monic])
    have := ar.finite
    have : Fact (Irreducible (X ^ 2 - C x)) := Fact.mk <| by
      simpa [← X_sq_sub_C_irreducible_iff_not_isSquare] using hx₂
    rcases adj_sqrt_ordered hx hx₂ with ⟨_, _, _⟩
    have := h (AdjoinRoot (X ^ 2 - C x))
    simp [ar.finrank_eq_natDegree] at this
  exists_isRoot_of_odd_natDegree {f} hf := by
    refine Polynomial.has_root_of_monic_odd_natDegree_imp_not_irreducible ?_ hf
    intro f hf_monic hf_odd hf_deg hf_irr
    have ar := AdjoinRoot.isAdjoinRootMonic' hf_monic
    rw [← ar.finrank_eq_natDegree] at *
    have := ar.finite
    have := Fact.mk hf_irr
    rcases odd_deg_ordered hf_odd with ⟨_, _, _⟩
    exact hf_deg (h (AdjoinRoot f))

end IsRealClosed
