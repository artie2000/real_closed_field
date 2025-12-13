/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.Algebra.Order.Cone.Order
import RealClosedField.Algebra.Order.Ring.Ordering.Basic

/-!
# Equivalence between orderings and order structures

## Main definitions

* `Field.ringOrderingLinearOrderEquiv`: equivalence between orderings on a field `F` and
linearly ordered field structures on `F`.
* `Ring.ringOrderingLinearOrderEquiv`: equivalence between orderings `O` on a ring `R` and
linearly ordered field structures on the domain `R ⧸ O.support`.

-/

namespace Field

variable {F : Type*} [Field F]

variable (F) in
open Classical in
/-- Equivalence between orderings on a field `F` and linearly ordered field structures on `F`. -/
noncomputable def ringOrderingLinearOrderEquiv :
    Equiv {O : Subsemiring F // O.IsOrdering}
          {o : LinearOrder F // IsStrictOrderedRing F} where
  toFun := fun ⟨O, hO⟩ =>
    let ⟨o, ho⟩ := Ring.isConeLinearOrderEquiv F ⟨O, inferInstance, inferInstance⟩
    ⟨o, IsOrderedRing.toIsStrictOrderedRing F⟩
  invFun := fun ⟨o, ho⟩ =>
    let ⟨O, hO⟩ := (Ring.isConeLinearOrderEquiv F).symm ⟨o, inferInstance⟩
    have := hO.1; have := hO.2; ⟨O, inferInstance⟩
  left_inv := fun ⟨_, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by ext; simp

@[simp]
theorem ringOrderingLinearOrderEquiv_apply (O : Subsemiring F) (h : O.IsOrdering) :
    (ringOrderingLinearOrderEquiv F ⟨O, h⟩ : LinearOrder F) =
    Ring.isConeLinearOrderEquiv F ⟨O, inferInstance, inferInstance⟩ := by
  simp [ringOrderingLinearOrderEquiv]

@[simp]
theorem ringOrderingLinearOrderEquiv_symm_apply_val
    (o : LinearOrder F) (h : IsStrictOrderedRing F) :
    ((ringOrderingLinearOrderEquiv F).symm ⟨o, h⟩ : Subsemiring F) =
    (Ring.isConeLinearOrderEquiv F).symm ⟨o, inferInstance⟩ := by
  simp [ringOrderingLinearOrderEquiv]

end Field

-- TODO : `Ring.ringOrderingLinearOrderEquiv` from unfinished part of `Algebra.Order.Cone.Order`
