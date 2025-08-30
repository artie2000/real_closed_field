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

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

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
  rcases Field.exists_primitive_element R K with ⟨α, hα⟩
  have := IsAdjoinRootMonic.mkOfPrimitiveElement (Algebra.IsIntegral.isIntegral α) hα
  rw [this.finrank] at *
  rcases exists_isRoot_of_odd_natDegree (Nat.not_even_iff_odd.mp hodd) with ⟨x, hx⟩
  exact hK <| Polynomial.natDegree_eq_of_degree_eq_some <|
    Polynomial.degree_eq_one_of_irreducible_of_root
      (minpoly.irreducible <| Algebra.IsIntegral.isIntegral α) hx

noncomputable def isAdjoinRootIOfFinrankExtensionEqTwo (hK : Module.finrank R K = 2) :
    IsAdjoinRoot K (X ^ 2 + 1 : R[X]) := by sorry

theorem finrank_adjoinRoot_i_extension_neq_two
    {K : Type*} [Field K] [Algebra (AdjoinRoot (X ^ 2 - C (-1) : R[X])) K] :
    Module.finrank (AdjoinRoot (X ^ 2 - C (-1) : R[X])) K ≠ 2 := by sorry

theorem finite_extension_classify :
    Nonempty (IsAdjoinRoot K (X ^ 2 + 1 : R[X])) ∨ Nonempty (IsAdjoinRoot K (1 : R[X])) := by sorry

end finite_ext

theorem algebraic_extension_classify
    {K : Type*} [Field K] [Algebra R K] [Algebra.IsAlgebraic R K] :
    Nonempty (IsAdjoinRoot K (X ^ 2 + 1 : R[X])) ∨ Nonempty (IsAdjoinRoot K (1 : R[X])) := by sorry

noncomputable def isAdjoinRootIOfIsAlgClosure
    {K : Type*} [Field K] [Algebra R K] [IsAlgClosure R K] :
    IsAdjoinRoot K (X ^ 2 + 1 : R[X]) := by sorry

end properties

/-! # Sufficient conditions to be real closed -/

theorem of_isAdjoinRoot_i_or_1_extension
    (h : ∀ {K : Type*}, [Field K] → [Algebra R K] → [FiniteDimensional R K] →
       (IsAdjoinRoot K (X ^ 2 + 1 : R[X]) ⊕ IsAdjoinRoot K (1 : R[X]))) :
    IsRealClosed R where
  isSquare_of_nonneg {x} hx := by sorry
  exists_isRoot_of_odd_natDegree {f} hf := by sorry

theorem of_IntermediateValueProperty
    (h : ∀ (f : R[X]) (x y : R), x ≤ y → 0 ≤ f.eval x → f.eval y ≤ 0 →
       ∃ z ∈ Set.Icc x y, f.eval z = 0) :
    IsRealClosed R where
  isSquare_of_nonneg {x} hx := by sorry
  exists_isRoot_of_odd_natDegree {f} hf := by sorry

theorem of_maximalIsOrderedAlgebra
    (h : ∀ {K : Type*}, [Field K] → [LinearOrder K] → [IsOrderedRing K] →
       [Algebra R K] → [IsOrderedAlgebra R K] → IsAdjoinRoot K (1 : R[X])) :
    IsRealClosed R where
  isSquare_of_nonneg {x} hx := by sorry
  exists_isRoot_of_odd_natDegree {f} hf := by sorry

end IsRealClosed
