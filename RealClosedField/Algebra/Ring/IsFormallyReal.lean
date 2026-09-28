/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.Algebra.Group.Submonoid.Support
import Mathlib.Algebra.Ring.IsFormallyReal

namespace IsFormallyReal

variable {R : Type*}

-- #44288 at `Mathlib.Algebra.Ring.SumsOfSquares`
@[simp]
theorem Subsemiring.sumSq_toAddSubmonoid {T : Type*} [CommSemiring T] :
    (Subsemiring.sumSq T).toAddSubmonoid = .sumSq T := by ext; simp

-- #44288
variable (R) in
protected theorem AddSubmonoid.IsPointed.sumSq [CommRing R] [IsFormallyReal R] :
    (AddSubmonoid.sumSq R).IsPointed := fun _ ↦ by
  simpa using IsFormallyReal.eq_zero_of_isSumSq_of_neg_isSumSq

-- #44288
variable (R) in
protected theorem Subsemiring.IsPointed.sumSq [CommRing R] [IsFormallyReal R] :
    (Subsemiring.sumSq R).IsPointed := by
  simpa using AddSubmonoid.IsPointed.sumSq R

end IsFormallyReal
