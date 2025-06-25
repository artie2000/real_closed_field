/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.RingTheory.Algebraic.Defs

/- An ordered R-algebra is an R-algebra whose algebra map is order-preserving. -/
class OrderedAlgebra (R A : Type*) [CommSemiring R] [Semiring A] [LinearOrder R] [LinearOrder A]
    [IsOrderedRing R] [IsOrderedRing A] extends Algebra R A where
  monotone' := Monotone algebraMap

/- An ordered field is real closed if every nonegative element is a square and
   every odd-degree polynomial has a root. -/
class IsRealClosed (R : Type*) [Field R] [LinearOrder R] [IsOrderedRing R] : Prop where
  isSquare_of_nonneg' {x : R} (hx : x ≥ 0) : IsSquare x
  exists_isRoot_of_odd_natDegree' {f : Polynomial R} (hf : Odd f.natDegree) : ∃ x, f.IsRoot x

/- A real closure is a real closed ordered algebraic extension. -/
class IsRealClosure (K R : Type*) [Field K] [Field R] [LinearOrder K] [LinearOrder R]
    [IsOrderedRing K] [IsOrderedRing R] [OrderedAlgebra K R] where
  isRealClosed : IsRealClosed K
  isAlgebraic : Algebra.IsAlgebraic K R
