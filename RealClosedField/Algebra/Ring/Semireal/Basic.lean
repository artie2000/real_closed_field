/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.Algebra.Order.Ring.Ordering.Defs
import RealClosedField.Upstream
import Mathlib.Algebra.Ring.Semireal.Defs

/-!
# Properties of semireal rings

We prove basic properties of semireal rings, such as their relationship to formally real rings.
-/

variable (R : Type*)

section CommRing

variable [CommRing R]

theorem Subsemiring.IsPreordering.sumSq [IsSemireal R] : (Subsemiring.sumSq R).IsPreordering where
  mem_of_isSquare h := by simpa using IsSquare.isSumSq h
  neg_one_notMem := by simpa using IsSemireal.not_isSumSq_neg_one R

variable {R} in
theorem isSemireal_ofIsPreordering {P : Subsemiring R} (hP : P.IsPreordering) : IsSemireal R :=
  .of_not_isSumSq_neg_one (hP.neg_one_notMem <| hP.mem_of_isSumSq ·)

variable {R} in
theorem exists_isPreordering_iff_isSemireal :
    (∃ P : Subsemiring R, P.IsPreordering) ↔ IsSemireal R where
  mp | ⟨_, hP⟩ => isSemireal_ofIsPreordering hP
  mpr _ := ⟨_, Subsemiring.IsPreordering.sumSq R⟩

end CommRing
