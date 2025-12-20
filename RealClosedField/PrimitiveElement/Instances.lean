/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.PrimitiveElement.PrimitiveElement
import Mathlib

-- TODO : ensure all material from `Mathlib.RingTheory.Adjoin.PowerBasis` is transferred
-- TODO : rewrite `Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed` to use my definitions

-- TODO : move to `Mathlib.FieldTheory.Minpoly.Field`
theorem Field.isIntegralUnique {R S : Type*} [Field R] [Ring S] [Algebra R S] {x : R}
    (h₁ : IsIntegral R x) : IsIntegralUnique x (minpoly R x) :=
  .of_aeval_eq_zero_imp_minpoly_dvd h₁ (minpoly.dvd R x)

-- TODO : move to `Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed`
theorem IsIntegrallyClosed.isIntegralUnique
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [Algebra R S]
    [IsDomain S] [NoZeroSMulDivisors R S] [IsIntegrallyClosed R] {x : S}
    (h₁ : IsIntegral R x) : IsIntegralUnique x (minpoly R x) :=
  .of_aeval_eq_zero_imp_minpoly_dvd h₁ (minpoly.isIntegrallyClosed_dvd h₁)

-- TODO : move adjoin lemmas to somewhere like `Mathlib.RingTheory.Adjoin.PowerBasis`

namespace Algebra.adjoin

theorem isIntegral [Algebra.IsIntegral R S] (s : Set S) :
    Algebra.IsIntegral R ↥(Algebra.adjoin R s) :=
  (Subalgebra.isIntegral_iff _).mpr (fun x _ ↦ Algebra.IsIntegral.isIntegral x)

@[simp]
theorem ker_aeval :
    RingHom.ker (aeval ⟨x, by aesop⟩ : R[X] →ₐ[R] ↥(adjoin R {x})) = RingHom.ker (aeval x) := by
  -- TODO : clean this proof up
  have : RingHomClass.toRingHom (aeval x) =
            (RingHomClass.toRingHom (Subalgebra.val (Algebra.adjoin R {x}))).comp
            (RingHomClass.toRingHom (aeval ⟨x, by aesop⟩ : R[X] →ₐ[R] ↥(adjoin R {x}))) := by
    ext a
    simp
    simp
  rw [AlgHom.ker_coe (aeval x), this, RingHom.ker_comp_of_injective, AlgHom.ker_coe]
  simp

theorem aeval_minpoly :
    (aeval ⟨x, by aesop⟩ : R[X] →ₐ[R] ↥(adjoin R {x})) (minpoly R x) = 0 := by
  rw [← RingHom.mem_ker]
  simp

variable {R x} in
theorem isIntegral_elem (hx : IsIntegral R x) :
    IsIntegral R (⟨x, by aesop⟩ : ↥(adjoin R {x})) :=
  ⟨minpoly R x, minpoly.monic hx, aeval_minpoly R x⟩

theorem isGenerator : IsGenerator R (⟨x, by aesop⟩ : ↥(adjoin R {x})) where
  adjoin_eq_top := Subalgebra.map_injective (f := (adjoin R {x}).val) Subtype.val_injective
    (by simp [Subalgebra.range_val])

variable {R x} in
theorem hasPrincipalKerAeval {f : R[X]} (h : RingHom.ker (aeval x) = Ideal.span {f}) :
    HasPrincipalKerAeval (⟨x, by aesop⟩ : ↥(adjoin R {x})) f where
  __ := isGenerator R x
  ker_aeval := by simp [h]

variable {R x} in
theorem isIntegralUnique (hx : IsIntegralUnique R x) :
    IsIntegralUnique R (⟨x, by aesop⟩ : ↥(adjoin R {x})) :=
  .of_ker_aeval_eq_span_monic (minpoly.monic hx.isIntegral) (by simp [hx.ker_aeval])

variable {R x} in
theorem hasPrincipalKerAevalIntegral (hx : IsIntegralUnique R x) :
    HasPrincipalKerAevalIntegral R (⟨x, by aesop⟩ : ↥(adjoin R {x})) :=
  .of_isIntegralUnique (Algebra.adjoin.isIntegralUnique hx) (Algebra.adjoin.isGenerator R x)

end Algebra.adjoin

#min_imports
