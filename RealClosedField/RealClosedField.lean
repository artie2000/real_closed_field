/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.OrderedAlgebra
import RealClosedField.Algebra.Ring.Semireal.Field

open Polynomial

/- An ordered field is real closed if every nonegative element is a square and
   every odd-degree polynomial has a root. -/
class IsRealClosed (R : Type*) [Field R] [LinearOrder R] : Prop extends IsStrictOrderedRing R where
  isSquare_of_nonneg {x : R} (hx : 0 ≤ x) : IsSquare x
  exists_isRoot_of_odd_natDegree {f : R[X]} (hf : Odd f.natDegree) : ∃ x, f.IsRoot x

/- A real closure is a real closed ordered algebraic extension. -/
class IsRealClosure (K R : Type*) [Field K] [Field R] [LinearOrder K] [LinearOrder R] [Algebra K R]
    [IsStrictOrderedRing K] extends IsRealClosed R, IsOrderedAlgebra K R, Algebra.IsAlgebraic K R

namespace IsRealClosed

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

section properties

variable [IsRealClosed R]

noncomputable def unique_isStrictOrderedRing :
    Unique {l : LinearOrder R // @IsStrictOrderedRing R _ (l.toPartialOrder)} where
  default := ⟨inferInstance, inferInstance⟩
  uniq := by
    suffices ∃! l : LinearOrder R, @IsStrictOrderedRing R _ (l.toPartialOrder) from fun ⟨l, hl⟩ ↦
      Subtype.ext <| ExistsUnique.unique this hl inferInstance
    rw [IsStrictOrderedRing.unique_isStrictOrderedRing_iff]
    aesop (add unsafe isSquare_of_nonneg)

/-! # Classification of extensions of a real closed field -/

section finite_ext

variable {K : Type*} [Field K] [Algebra R K] [FiniteDimensional R K]

theorem even_finrank_extension (hK : Module.finrank R K ≠ 1) : Even (Module.finrank R K) := by
  by_contra hodd
  rcases Field.isAdjoinRootMonic R K with ⟨f, hf⟩
  rw [hf.finrank] at *
  rcases exists_isRoot_of_odd_natDegree (f := f)
    (Nat.not_even_iff_odd.mp <| by simpa using hodd) with ⟨x, hx⟩
  exact hK <| by simpa using natDegree_eq_of_degree_eq_some <|
    degree_eq_one_of_irreducible_of_root hf.irreducible hx

-- TODO : find a way to go between `X ^ 2 - C (-1)` and `X ^ 2 + 1` in `IsSimpleGenerator`
noncomputable def isAdjoinRootIOfFinrankExtensionEqTwo [IsQuadraticExtension K R] :
    IsAdjoinRoot K (X ^ 2 + 1 : R[X]) := by sorry

theorem finrank_adjoinRoot_i_extension_neq_two
    {K : Type*} [Field K] [Algebra (AdjoinRoot (X ^ 2 + 1 : R[X])) K] :
    Module.finrank (AdjoinRoot (X ^ 2 + 1 : R[X])) K ≠ 2 := fun hK ↦ by sorry

theorem finite_extension_classify :
    IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X])) ∨ Module.finrank R K = 1 := by sorry

end finite_ext

theorem algebraic_extension_classify
    {K : Type*} [Field K] [Algebra R K] [Algebra.IsAlgebraic R K] :
    IsAdjonRootMonic' K (X ^ 2 + 1 : R[X]) ∨ Module.finrank R K = 1 := by sorry

noncomputable def isAdjoinRootIOfIsAlgClosure
    {K : Type*} [Field K] [Algebra R K] [IsAlgClosure R K] :
    IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X]) := by sorry

end properties

/-! # Sufficient conditions to be real closed -/

theorem of_isAdjoinRoot_i_or_1_extension
    (h : ∀ K : Type u, [Field K] → [Algebra R K] → [FiniteDimensional R K] →
       Nonempty (IsAdjoinRoot K (X ^ 2 - C (-1) : R[X])) ∨ Module.finrank R K = 1) :
    IsRealClosed R where
  isSquare_of_nonneg {x} hx := by
    by_contra hx₂
    have ar := AdjoinRoot.isAdjoinRootMonic (X ^ 2 - C x) (by simp [Monic])
    have := ar.finite
    have : Fact (Irreducible (X ^ 2 - C x)) := Fact.mk <| by
      simpa [← X_sq_sub_C_irreducible_iff_not_isSquare] using hx₂
    cases h (AdjoinRoot (X ^ 2 - C x)) with
    | inl h_ext =>
      exact h_ext.elim <| fun ar' ↦ by
        let ar' := IsAdjoinRootMonic.mk ar' (by simp [Monic])
        have cal : ar.coeff (ar'.root ^ 2) 0 = ar.coeff (-1) 0 := by simp
        simp [- IsAdjoinRoot.Quadratic.sq_root, pow_two] at cal
        have : 0 ≤ ar.coeff ar'.root 0 ^ 2 + x * ar.coeff ar'.root 1 ^ 2 := by positivity
        simp [pow_two] at this
        linarith
        -- TODO : clean this computation up
    | inr h_ext => simp [ar.finrank] at h_ext
    -- TODO : code reused at `of_maximalIsOrderedAlgebra`; abstract it
  exists_isRoot_of_odd_natDegree {f} hf := by
    refine Polynomial.has_root_of_odd_natDegree_imp_not_irreducible ?_ hf
    intro f hf_odd hf_deg hf_irr
    -- TODO : generalise IsAdjoinRootMonic.finrank to IsAdjoinRoot to get rid of this `normalize` and associated rewrites
    have ar := AdjoinRoot.isAdjoinRootMonic (normalize f)
      (Polynomial.monic_normalize hf_irr.ne_zero)
    rw [← (show _ = f.natDegree by simpa using ar.finrank)] at *
    rw [← Associated.irreducible_iff (normalize_associated f)] at hf_irr
    have := Fact.mk hf_irr
    have := Module.finite_of_finrank_pos hf_odd.pos
    cases h <| AdjoinRoot (normalize f) with
    | inl h_ext => exact h_ext.elim <|
        fun ar' ↦ by simp [(IsAdjoinRootMonic.mk ar' (by simp [Monic])).finrank] at hf_odd; grind
    | inr h_ext => exact hf_deg h_ext

theorem of_IntermediateValueProperty
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
        (by simpa using hy) (by simpa using hx) (by linarith)
    rcases h f _ _ hxy (by linarith) (by linarith) with ⟨z, _, hz⟩
    exact ⟨z, hz⟩

theorem of_maximalIsOrderedAlgebra
    (h : ∀ K : Type u, [Field K] → [LinearOrder K] → [IsOrderedRing K] → [Algebra R K] →
           [FiniteDimensional R K] → [IsOrderedAlgebra R K] → Module.finrank R K = 1) :
    IsRealClosed R where
  isSquare_of_nonneg {x} hx := by
    by_contra hx₂
    rcases adj_sqrt_ordered hx hx₂ with ⟨_, _, _⟩

    -- TODO : remove / automate / regularise this boilerplate
    have ar := AdjoinRoot.isAdjoinRootMonic (X ^ 2 - C x) (by simp [Monic])
    have := ar.finite
    have : Fact (Irreducible (X ^ 2 - C x)) := Fact.mk <| by
      simpa [← X_sq_sub_C_irreducible_iff_not_isSquare] using hx₂
    -- end boilerplate

    have := h (AdjoinRoot (X ^ 2 - C x))
    simp [ar.finrank] at this -- TODO : find out why this works

  exists_isRoot_of_odd_natDegree {f} hf := by
    refine Polynomial.has_root_of_odd_natDegree_imp_not_irreducible ?_ hf
    intro f hf_odd hf_deg hf_irr
    -- TODO : generalise IsAdjoinRootMonic.finrank to IsAdjoinRoot to get rid of this `normalize` and associated rewrites
    have ar := AdjoinRoot.isAdjoinRootMonic (normalize f)
      (Polynomial.monic_normalize hf_irr.ne_zero)
    rw [← (show _ = f.natDegree by simpa using ar.finrank)] at *
    rw [← Associated.irreducible_iff (normalize_associated f)] at hf_irr
    have := Fact.mk hf_irr
    have := Module.finite_of_finrank_pos hf_odd.pos
    rcases odd_deg_ordered hf_odd with ⟨_, _, _⟩
    exact hf_deg <| h <| AdjoinRoot (normalize f)
    -- TODO : factor out boilerplate (reused from `of_isAdjoinRoot_i_or_1_extension`)

end IsRealClosed
