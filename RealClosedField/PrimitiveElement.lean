/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.PowerBasis

-- relevant file: Mathlib.RingTheory.Adjoin.PowerBasis

open Polynomial algebraMap

attribute [simp] Algebra.self_mem_adjoin_singleton

def IsPrimitiveElem (R : Type*) {S : Type*} [CommRing R] [Ring S] [Algebra R S] (x : S) : Prop :=
  Algebra.adjoin R {x} = ⊤

namespace IsPrimitiveElem

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S] {x : S}

theorem of_adjoin_eq_top (hx : Algebra.adjoin R {x} = ⊤) : IsPrimitiveElem R x := hx

variable (x) in
theorem _root_.Algebra.adjoin.isPrimitiveElem :
    IsPrimitiveElem R (⟨x, Algebra.self_mem_adjoin_singleton R x⟩ : ↥(Algebra.adjoin R {x})) :=
  IsPrimitiveElem.of_adjoin_eq_top <| by
  ext ⟨y, hy⟩
  simp
  -- TODO : can this induction be removed?
  induction hy using Algebra.adjoin_induction with
  | mem _ hx' => simp [by simpa using hx']
  | algebraMap => simp
  | add z w _ _ hz hw => exact Subalgebra.add_mem _ hz hw
  | mul z w _ _ hz hw => exact Subalgebra.mul_mem _ hz hw

variable (hx : IsPrimitiveElem R x)

include hx in
theorem adjoin_eq_top : Algebra.adjoin R {x} = ⊤ := hx

include hx in
@[simp]
theorem mem_adjoin (y : S) : y ∈ Algebra.adjoin R {x} := by simp [hx.adjoin_eq_top]

include hx in
theorem aeval_surjective : Function.Surjective (aeval x : R[X] →ₐ[R] S) :=
  (Algebra.adjoin_mem_exists_aeval _ _ <| hx.mem_adjoin ·)

include hx in
noncomputable def equivAdjoin : ↥(Algebra.adjoin R {x}) ≃ₐ[R] S :=
  (Subalgebra.equivOfEq _ _ hx).trans Subalgebra.topEquiv

theorem equivAdjoin_apply (y : ↥(Algebra.adjoin R {x})) : hx.equivAdjoin y = ↑y := rfl

theorem equivAdjoin_symm_apply (y : S) : hx.equivAdjoin.symm y = ⟨y, hx.mem_adjoin y⟩ := rfl

end IsPrimitiveElem
