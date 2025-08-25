/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.OrderedAlgebra

/- An ordered field is real closed if every nonegative element is a square and
   every odd-degree polynomial has a root. -/
class IsRealClosed (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] : Prop where
  isSquare_of_nonneg' {x : R} (hx : 0 ≤ x) : IsSquare x
  exists_isRoot_of_odd_natDegree' {f : Polynomial R} (hf : Odd f.natDegree) : ∃ x, f.IsRoot x

/- A real closure is a real closed ordered algebraic extension. -/
class IsRealClosure (K R : Type*) [Field K] [Field R] [LinearOrder K] [LinearOrder R]
    [IsStrictOrderedRing K] [IsStrictOrderedRing R] [Algebra K R]
    extends IsOrderedAlgebra K R, Algebra.IsAlgebraic K R, IsRealClosed K

#min_imports
