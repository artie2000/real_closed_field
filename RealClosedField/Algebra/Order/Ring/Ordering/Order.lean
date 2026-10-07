/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.Algebra.Order.Ring.Ordering.Basic

/-!
# Equivalence between orderings and order structures

## Main definitions

* `Field.isOrderingLinearOrderEquiv`: equivalence between orderings on a field `F` and
linearly ordered field structures on `F`.
* `Ring.isOrderingLinearOrderEquiv`: equivalence between orderings `O` on a ring `R` and
linearly ordered field structures on the domain `R ⧸ O.support`.

-/

namespace Field

variable {F : Type*} [Field F]

variable (F) in
open Classical in
/-- Equivalence between orderings on a field `F` and linearly ordered field structures on `F`. -/
noncomputable def isOrderingLinearOrderEquiv :
    Equiv {O : Subsemiring F // O.IsOrdering}
          {_o : LinearOrder F // IsStrictOrderedRing F} where
  toFun := fun ⟨O, hO⟩ ↦
    let ⟨o, ho⟩ := Ring.isPointedLinearOrderEquiv F
      ⟨O, hO.isPreordering.isPointed, hO.isSpanning⟩
    ⟨o, IsOrderedRing.toIsStrictOrderedRing F⟩
  invFun := fun ⟨o, ho⟩ ↦
    let ⟨O, hO⟩ := (Ring.isPointedLinearOrderEquiv F).symm ⟨o, inferInstance⟩
    ⟨O, Subsemiring.IsOrdering.of_isSpanning_of_isPointed hO.2 hO.1⟩
  left_inv := fun ⟨_, _⟩ ↦ by ext; simp
  right_inv := fun ⟨_, _⟩ ↦ by
    -- TODO : fix proj-reduction with classes, simp, extends-projection
    ext : 1
    simp
    ext
    simp

@[simp]
theorem isOrderingLinearOrderEquiv_apply (O : Subsemiring F) (h : O.IsOrdering) :
    (isOrderingLinearOrderEquiv F ⟨O, h⟩ : LinearOrder F) =
    Ring.isPointedLinearOrderEquiv F ⟨O, h.isPreordering.isPointed, h.isSpanning⟩ := by
  simp [isOrderingLinearOrderEquiv]

@[simp]
theorem isOrderingLinearOrderEquiv_symm_apply_val
    (o : LinearOrder F) (h : IsStrictOrderedRing F) :
    ((isOrderingLinearOrderEquiv F).symm ⟨o, h⟩ : Subsemiring F) =
    (Ring.isPointedLinearOrderEquiv F).symm ⟨o, inferInstance⟩ := by
  simp [isOrderingLinearOrderEquiv]

end Field

-- TODO : `Ring.isOrderingLinearOrderEquiv` from unfinished part of `Algebra.Order.Cone.Order`
