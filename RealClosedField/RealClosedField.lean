/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.OrderedAlgebra
import RealClosedField.Algebra.Order.Field.Semireal
import Mathlib.Algebra.Polynomial.SpecificDegree

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

variable (R) in
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
  rcases lt_or_ge 0 a with (pos | neg)
  · absurd (show ¬ IsSquare a by
      simpa [Polynomial.X_sq_sub_C_irreducible_iff_not_isSquare] using hK.irreducible)
    exact isSquare_of_nonneg pos.le
  · simpa using IsAdjoinRootMonic'.of_isAdjoinRootMonic_of_isSquare_div (a₂ := -1)
      (by simp) (isSquare_of_nonneg (by field_simp; linarith)) hK

-- TODO : proper sqrt operation + API?
theorem isSquare_of_isAdjoinRoot_i (hK : IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X]))
    (x : K) : IsSquare x := by
  let i := hK.root -- prevents the `X ^ 2 + 1` argument being rewritten
  have hRi : IsIntegralGenSqrt i (-1 : R) := ⟨by simpa using hK.pe⟩
  rw [hRi.self_eq_coeff x]
  rcases eq_or_ne (hRi.coeff x 1) 0 with (zero | ne)
  · rw [zero]
    suffices IsSquare (algebraMap _ _ (hRi.coeff x 0)) by
      aesop (erase simp AdjoinRoot.algebraMap_eq)
    rcases isSquare_or_isSquare_neg (hRi.coeff x 0) with (pos | neg)
    · aesop
    · have : IsSquare (-1 : K) := ⟨i, by simp [← pow_two, hRi.sq_root]⟩
      simpa using IsSquare.mul this (IsSquare.map (algebraMap _ _) neg)
  · rcases isSquare_of_nonneg (by positivity : 0 ≤ (hRi.coeff x 0) ^ 2 + (hRi.coeff x 1) ^ 2)
      with ⟨rt₁, hrt₁⟩
    have : - |rt₁| < (hRi.coeff x 0) :=
      (abs_lt_of_sq_lt_sq' (by simp [pow_two, ← hrt₁, ne]) (by simp)).1
    have : 0 < (hRi.coeff x 0) + |rt₁| := by linarith
    rcases isSquare_of_nonneg (by positivity : 0 ≤ ((hRi.coeff x 0) + |rt₁|) / 2)
      with ⟨rt₂, hrt₂⟩
    have : algebraMap _ K |rt₂| ≠ 0 := fun hc ↦ by simp_all
    have : (2 : K) ≠ 0 := by
      -- TODO : add lemma about `CharZero` being preserved by algebra extensions
      have : CharZero K := by
        simp [← Algebra.ringChar_eq R, ← CharP.ringChar_zero_iff_CharZero]
      exact two_ne_zero
    use algebraMap _ _ |rt₂| + algebraMap _ _ (hRi.coeff x 1 / (2 * |rt₂|)) * i
    simp [-AdjoinRoot.algebraMap_eq, map_ofNat]
    field_simp
    have : algebraMap _ K |rt₂| ^ 2 =
           algebraMap _ _ ((hRi.coeff x 0 + |rt₁|) / 2) := by
      rw [← map_pow, sq_abs, pow_two rt₂, ← hrt₂]
    rw [this]
    simp [-AdjoinRoot.algebraMap_eq, map_ofNat]
    field_simp
    ring_nf
    simp [hRi.sq_root, -AdjoinRoot.algebraMap_eq]
    ring_nf
    have : algebraMap _ K |rt₁| ^ 2 =
           algebraMap _ _ (hRi.coeff x 0 ^ 2 + hRi.coeff x 1 ^ 2) := by
      rw [← map_pow, sq_abs, pow_two rt₁, ← hrt₁]
    rw [this]
    simp [-AdjoinRoot.algebraMap_eq]
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
theorem maximal_isOrderedField [LinearOrder K] [IsOrderedRing K] [Algebra.IsAlgebraic R K] :
    Module.finrank R K = 1 := by
  rcases finite_extension_classify R K with (sq | triv)
  · have sqrt : IsIntegralGenSqrt sq.root (-1 : R) := ⟨by simpa using sq.pe⟩
    absurd (show ¬ IsSquare (-1 : K) by simp)
    exact ⟨sq.root, by simpa [pow_two] using sqrt.sq_root.symm⟩
  · exact triv

variable (K) in
theorem isAdjoinRoot_i_of_isAlgClosure [IsAlgClosure R K] :
    IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X]) := by
  rcases finite_extension_classify R K with (sq | triv)
  · exact sq
  · have : IsAlgClosed K := ‹IsAlgClosure _ K›.isAlgClosed
    rw [← Module.nonempty_algEquiv_iff_finrank_eq_one] at triv
    have := IsSquare.map triv.some.symm (IsAlgClosed.isSquare (-1 : K))
    simp_all

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
    rcases finite_extension_classify R (AdjoinRoot f) with (sq | triv)
    · apply Or.inr
      have iu : IsIntegralGenSqrt _ (-1 : R) := ⟨by simpa using sq.pe⟩
      set r := sq.root with hr
      have eq_root := iu.self_eq_coeff (AdjoinRoot.root f)
      refine ⟨iu.coeff (AdjoinRoot.root f) 0, iu.coeff (AdjoinRoot.root f) 1, fun hc ↦ ?_, ?_⟩
      · simp [hc] at eq_root
        sorry -- contradiction at eq_root
      · suffices AdjoinRoot.mk f ((X - C (iu.coeff (AdjoinRoot.root f) 0)) ^ 2 +
                                 C (iu.coeff (AdjoinRoot.root f) 1) ^ 2) = 0 by
          rw [AdjoinRoot.mk_eq_zero] at this
          refine Polynomial.eq_of_dvd_of_natDegree_le_of_leadingCoeff this ?_ (by simp [hf]; sorry)
          sorry
        simp [← AdjoinRoot.algebraMap_eq]
        nth_rw 1 [eq_root]
        ring_nf
        simp [iu.sq_root]
    · simp_all [(AdjoinRoot.powerBasis hf.ne_zero).finrank] -- TODO : update to my notation
  mpr h := by
    rcases h with (lin | quad)
    · exact Polynomial.irreducible_of_degree_eq_one
        (by simpa [Polynomial.natDegree_eq_one_iff_degree_eq_one] using lin)
    · rcases quad with ⟨a, b, hb, rfl⟩
      have h_deg : ((X - C a) ^ 2 + C b ^ 2).natDegree = 2 := by sorry
      rw [hf.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega),
          Polynomial.roots_eq_zero_iff_isRoot_eq_bot hf.ne_zero]
      ext r
      suffices (r - a) ^ 2 + b ^ 2 ≠ 0 by simp [this]
      intro hc
      have : b ^ 2 = 0 := by linarith [sq_nonneg b, sq_nonneg (r - a)]
      simp_all

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

theorem of_isAdjoinRoot_i_algebraicClosure
    (h : IsAdjoinRootMonic' (AlgebraicClosure R) (X ^ 2 + 1 : R[X])) : IsRealClosed R :=
  of_isAdjoinRoot_i_or_finrank_eq_one fun K _ _ _ ↦ by
    rcases IsAlgClosed.nonempty_algEquiv_or_of_finrank_eq_two K
      (by simpa using h.finrank_eq_natDegree) with (hK | hK)
    · rw [Nonempty.congr AlgEquiv.symm AlgEquiv.symm,
          Module.nonempty_algEquiv_iff_finrank_eq_one] at hK
      exact Or.inr hK
    · exact Or.inl (h.map hK.some.symm)

theorem of_intermediateValueProperty
    (h : ∀ {f : R[X]} {x y : R}, x ≤ y → 0 ≤ f.eval x → f.eval y ≤ 0 →
       ∃ z ∈ Set.Icc x y, f.eval z = 0) :
    IsRealClosed R where
  isSquare_of_nonneg {x} hx := by
    have : x ≤ (x + 1) ^ 2 := by
      suffices 0 ≤ 1 + x + x ^ 2 by linear_combination this
      positivity
    rcases h (f := - X ^ 2 + C x) (x := 0) (y := x + 1)
      (by linarith) (by simpa using hx) (by simpa using this) with ⟨z, _, hz⟩
    exact ⟨z, by linear_combination (by simpa using hz : _ = (0 : R))⟩
  exists_isRoot_of_odd_natDegree {f} hf := by
    rcases sign_change hf with ⟨x, y, hx, hy⟩
    wlog hxy : y ≤ x
    · simpa using this h (f := -f) (by simpa using hf) y x
        (by simpa using hy) (by simpa using hx) (by order)
    rcases h hxy (by order) (by order) with ⟨z, _, hz⟩
    exact ⟨z, hz⟩

theorem of_maximal_isOrderedAlgebra
    (h : ∀ K : Type u, [Field K] → [LinearOrder K] → [IsStrictOrderedRing K] → [Algebra R K] →
           [Algebra.IsAlgebraic R K] → [IsOrderedModule R K] → Module.finrank R K = 1) :
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

variable (R) in
theorem TFAE :
    [IsRealClosed R,
     IsAdjoinRootMonic' (AlgebraicClosure R) (X ^ 2 + 1 : R[X]),
    (∀ K : Type u, [Field K] → [LinearOrder K] → [IsStrictOrderedRing K] → [Algebra R K] →
      [Algebra.IsAlgebraic R K] → [IsOrderedModule R K] → Module.finrank R K = 1),
    (∀ {f : R[X]} {x y : R}, x ≤ y → 0 ≤ f.eval x → f.eval y ≤ 0 →
      ∃ z ∈ Set.Icc x y, f.eval z = 0)].TFAE := by
  tfae_have 1 → 2 := fun _ ↦ isAdjoinRoot_i_of_isQuadraticExtension R (AlgebraicClosure R)
  tfae_have 1 → 3 := fun _ K ↦ maximal_isOrderedField R K
  tfae_have 1 → 4 := fun _ ↦ intermediate_value_property
  tfae_have 2 → 1 := of_isAdjoinRoot_i_algebraicClosure
  tfae_have 3 → 1 := of_maximal_isOrderedAlgebra
  tfae_have 4 → 1 := of_intermediateValueProperty
  tfae_finish

end IsRealClosed

-- TODO : move to right place
theorem IsSemireal.of_isAdjoinRoot_i_algebraicClosure {R : Type*} [Field R]
    (hR : IsAdjoinRootMonic' (AlgebraicClosure R) (X ^ 2 + 1 : R[X])) : IsSemireal R := by
  rw [isSemireal_iff_not_isSumSq_neg_one]
  intro hc
  have := hR.irreducible
  rw [show X ^ 2 + (1 : R[X]) = X ^ 2 - (C (-1)) by simp,
      Polynomial.X_sq_sub_C_irreducible_iff_not_isSquare] at this
  exact this <| isSumSq_of_isSquare hR IsAlgClosed.isSquare (-1 : R) hc

theorem IsSemireal.TFAE_RCF {F : Type u} [Field F] :
    [IsSemireal F ∧ (∀ x : F, IsSquare x ∨ IsSquare (-x)) ∧
     ∀ {f : F[X]}, Odd f.natDegree → ∃ x, f.IsRoot x,
     IsAdjoinRootMonic' (AlgebraicClosure F) (X ^ 2 + 1 : F[X]),
     IsSemireal F ∧
     (∀ K : Type u, [Field K] → [IsSemireal K] → [Algebra F K] → [Algebra.IsAlgebraic F K] →
      Module.finrank F K = 1)].TFAE := by
  tfae_have 1 → 2 := fun ⟨h₁, h₂, h₃⟩ ↦ by
    letI := IsSemireal.toLinearOrder F
    apply ((IsRealClosed.TFAE F).out 0 1).mp
    refine { isSquare_of_nonneg := fun {x} hx ↦ ?_, exists_isRoot_of_odd_natDegree := h₃ }
    rcases h₂ x with (triv | contr)
    · exact triv
    · have : x = 0 := by linarith [IsSquare.nonneg contr]
      simp_all
  tfae_have 2 → 3 := fun h ↦ by
    have := IsSemireal.of_isAdjoinRoot_i_algebraicClosure h
    refine ⟨this, ?_⟩
    letI := IsSemireal.toLinearOrder F
    -- we need the strong version of `IsRealClosed.TFAE [2]`
    have : IsRealClosed _ := ((IsRealClosed.TFAE F).out 1 0).mp h
    intro K
    intros
    letI := IsSemireal.toLinearOrder K
    exact IsRealClosed.maximal_isOrderedField F K
  tfae_have 3 → 1 := fun ⟨h₁, h₂⟩ ↦ by
    refine ⟨h₁, ?_⟩
    letI := IsSemireal.toLinearOrder F
    suffices IsRealClosed F from
      ⟨IsRealClosed.isSquare_or_isSquare_neg,
      IsRealClosed.exists_isRoot_of_odd_natDegree⟩
    refine ((IsRealClosed.TFAE F).out 2 0).mp (by exact fun K ↦ h₂ K)
  tfae_finish

theorem very_weak_Artin_Schreier {R : Type*} [Field R]
    (hR : IsAdjoinRootMonic' (AlgebraicClosure R) (X ^ 2 + 1 : R[X])) :
    ∃! l : LinearOrder R, ∃ _ : IsStrictOrderedRing R, IsRealClosed R := by
  have := IsSemireal.of_isAdjoinRoot_i_algebraicClosure hR
  rw [← Field.exists_isStrictOrderedRing_iff_isSemireal] at this
  rcases this with ⟨l, hl⟩
  have : IsRealClosed R := IsRealClosed.of_isAdjoinRoot_i_algebraicClosure hR
  have uniq := IsRealClosed.unique_isStrictOrderedRing R
  refine ⟨l, ⟨‹_›, ‹_›⟩, fun l' ⟨hl'₁, hl'₂⟩ ↦ ?_⟩
  grind [uniq.eq_default ⟨l, hl⟩, uniq.eq_default ⟨l', hl'₁⟩]

theorem weak_Artin_Schreier {R : Type*} [Field R] (hR_char : ringChar R ≠ 2)
    (hR : Module.finrank R (AlgebraicClosure R) = 2) :
    ∃! l : LinearOrder R, ∃ _ : IsStrictOrderedRing R, IsRealClosed R :=
  very_weak_Artin_Schreier <| by
  sorry

theorem Artin_Schreier {R : Type*} [Field R]
    (hR : FiniteDimensional R (AlgebraicClosure R)) :
    IsAlgClosed R ∨ ∃! l : LinearOrder R, ∃ _ : IsStrictOrderedRing R, IsRealClosed R :=
  sorry
