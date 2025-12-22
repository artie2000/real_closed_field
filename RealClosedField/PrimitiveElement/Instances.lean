/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.PrimitiveElement.PrimitiveElement

-- TODO : ensure all material from `Mathlib.RingTheory.Adjoin.PowerBasis` is transferred
-- TODO : rewrite `Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed` to use my definitions

open Polynomial

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

namespace AdjoinRoot

variable {R : Type*} [CommRing R] (f : R[X])

theorem isGenerator : Algebra.IsGenerator R (root f) := by
  rw [Algebra.isGenerator_iff_aeval_surjective]
  convert mk_surjective
  ext
  rw [aeval_eq]

theorem hasPrincipalKerAeval : Algebra.HasPrincipalKerAeval (root f) f where
  __ := isGenerator f
  ker_aeval := by
    ext
    simp [Ideal.mem_span_singleton]

variable {f} in
theorem isIntegralUniqueGen (hf : f.Monic) : IsIntegralUnique (root f) f where
  __ := hasPrincipalKerAeval f
  monic := hf

theorem isAdjoinRoot' : IsAdjoinRoot' (AdjoinRoot f) f := ⟨root f, hasPrincipalKerAeval f⟩

variable {f} in
theorem isAdjoinRootMonic' (hf : f.Monic) : IsAdjoinRootMonic' (AdjoinRoot f) f :=
  ⟨isAdjoinRoot' f, hf⟩

end AdjoinRoot

-- TODO : primitive element theorem

-- TODO : move adjoin lemmas to somewhere like `Mathlib.RingTheory.Adjoin.PowerBasis`

namespace Algebra.adjoin

variable (R : Type*) {S : Type*} [CommRing R] [Ring S] [Algebra R S] (x : S)

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
theorem hasPrincipalKerAeval {g : R[X]} (h : RingHom.ker (aeval x) = Ideal.span {g}) :
    HasPrincipalKerAeval (⟨x, by aesop⟩ : ↥(adjoin R {x})) g where
  __ := isGenerator R x
  ker_aeval := by simp [h]

variable {R x} in
theorem isIntegralUnique {g : R[X]} (hx : IsIntegralUnique x g) :
    IsIntegralUnique (⟨x, by aesop⟩ : ↥(adjoin R {x})) g where
  monic := hx.monic
  ker_aeval := by simp [hx.ker_aeval]

variable {R x} in
theorem isIntegralUniqueGen {g : R[X]}  (hx : IsIntegralUnique x g) :
    IsIntegralUniqueGen (⟨x, by aesop⟩ : ↥(adjoin R {x})) g where
  __ := hasPrincipalKerAeval hx.ker_aeval
  __ := isIntegralUnique hx

end Algebra.adjoin
