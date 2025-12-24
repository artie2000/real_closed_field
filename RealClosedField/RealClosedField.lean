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

theorem mk_monic
    (isSquare_of_nonneg : ∀ {x : R}, 0 ≤ x → IsSquare x)
    (exists_isRoot_of_odd_natDegree : ∀ {f : R[X]}, Odd f.natDegree → Monic f → ∃ x, f.IsRoot x) :
    IsRealClosed R where
  isSquare_of_nonneg := isSquare_of_nonneg
  exists_isRoot_of_odd_natDegree {f} hf := by
    rcases exists_isRoot_of_odd_natDegree (f := normalize f) (by simpa using hf)
        (Polynomial.monic_normalize (fun hc ↦ by simp_all)) with ⟨x, hx⟩
    exact ⟨x, hx.dvd (by simp)⟩

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
  rcases Field.exists_isAdjoinRootMonic R K with ⟨f, hf⟩
  rw [hf.finrank_eq_natDegree] at *
  rcases exists_isRoot_of_odd_natDegree (f := f)
    (Nat.not_even_iff_odd.mp <| by simpa using hodd) with ⟨x, hx⟩
  exact hK <| by simpa using natDegree_eq_of_degree_eq_some <|
    degree_eq_one_of_irreducible_of_root hf.irreducible hx

theorem isAdjoinRootIOfFinrankExtensionEqTwo [Algebra.IsQuadraticExtension R K] :
    IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X]) := by sorry

theorem finrank_adjoinRoot_i_extension_neq_two
    {K : Type*} [Field K] [Algebra (AdjoinRoot (X ^ 2 + 1 : R[X])) K] :
    Module.finrank (AdjoinRoot (X ^ 2 + 1 : R[X])) K ≠ 2 := fun hK ↦ by sorry

theorem finite_extension_classify :
    IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X]) ∨ Module.finrank R K = 1 := by sorry

end finite_ext

theorem algebraic_extension_classify
    {K : Type*} [Field K] [Algebra R K] [Algebra.IsAlgebraic R K] :
    IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X]) ∨ Module.finrank R K = 1 := by sorry

noncomputable def isAdjoinRootIOfIsAlgClosure
    {K : Type*} [Field K] [Algebra R K] [IsAlgClosure R K] :
    IsAdjoinRootMonic' K (X ^ 2 + 1 : R[X]) := by sorry

end properties

/-! # Sufficient conditions to be real closed -/

theorem of_isAdjoinRoot_i_or_1_extension
    (h : ∀ K : Type u, [Field K] → [Algebra R K] → [FiniteDimensional R K] →
       IsAdjoinRootMonic' K (X ^ 2 - C (-1) : R[X]) ∨ Module.finrank R K = 1) :
    IsRealClosed R where
  isSquare_of_nonneg {x} hx := by
    by_contra hx₂
    have iu := AdjoinRoot.isIntegralUniqueGen (f := X ^ 2 - C x) (by simp [Monic])
    have := iu.finite
    have : Fact (Irreducible (X ^ 2 - C x)) := Fact.mk <| by
      simpa [← X_sq_sub_C_irreducible_iff_not_isSquare] using hx₂
    rcases h (AdjoinRoot (X ^ 2 - C x)) with (ar' | fr)
    · have cal : iu.coeff (ar'.root ^ 2) 0 = iu.coeff (-1) 0 := by
        rw [IsIntegralUniqueGen.SqRoot.sq_root ar'.pe.toIsIntegralUnique]
      simp [-map_neg, pow_two ar'.root] at cal -- TODO : change to simp [pow_two] after abstraction fixed
      have : 0 ≤ iu.coeff ar'.root 0 ^ 2 + x * iu.coeff ar'.root 1 ^ 2 := by positivity
      simp [-map_neg, pow_two (iu.coeff ar'.root _)] at this -- TODO : change to simp [pow_two] after abstraction fixed
      linarith
      -- TODO : clean this computation up
    · simp [iu.finrank_eq_natDegree] at fr
    -- TODO : code reused at `of_maximalIsOrderedAlgebra`; abstract it
  exists_isRoot_of_odd_natDegree {f} hf := by
    refine Polynomial.has_root_of_monic_odd_natDegree_imp_not_irreducible ?_ hf
    intro f hf_monic hf_odd hf_deg hf_irr
    have iu := AdjoinRoot.isIntegralUniqueGen hf_monic
    rw [← (show _ = f.natDegree by simpa using iu.finrank_eq_natDegree)] at *
    have := Fact.mk hf_irr
    have := Module.finite_of_finrank_pos hf_odd.pos
    rcases h (AdjoinRoot f) with (ar' | fr)
    · simp [ar'.finrank_eq_natDegree] at hf_odd; grind
    · exact hf_deg fr

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
