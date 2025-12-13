/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import Mathlib.Algebra.Order.Monoid.Submonoid
import Mathlib.Algebra.Ring.Subsemiring.Order
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
import RealClosedField.Algebra.Order.Ring.Ordering.Basic
import RealClosedField.Algebra.Order.Cone

/-!

We demonstrate the equivalence of orderings on a commutative ring `R` and
linear ordered quotient domains of `R`. We also specialise to the case where `R` is a field.

## Main results

TODO : come up with the right names
-- equivalence between support-0 orderings and linear ordered ring
-- equivalence between orderings on field and linear ordered field
-- equivalence between orderings and linear ordered quotient domain

## References

- [*An introduction to real algebra*, T.Y. Lam][lam_1984]

-/

-- TODO : upstream the following

theorem Quotient.image_mk_eq_lift {α : Type*} {s : Setoid α} (A : Set α)
    (h : ∀ x y, x ≈ y → (x ∈ A ↔ y ∈ A)) :
    (Quotient.mk s) '' A = (Quotient.lift (· ∈ A) (by simpa)) := by
  aesop (add unsafe forward Quotient.exists_rep)

@[to_additive]
theorem QuotientGroup.mem_iff_mem_of_rel {G S : Type*} [CommGroup G]
    [SetLike S G] [MulMemClass S G] (H : Subgroup G) {M : S} (hM : (H : Set G) ⊆ M) :
    ∀ x y, QuotientGroup.leftRel H x y → (x ∈ M ↔ y ∈ M) := fun x y hxy => by
  rw [QuotientGroup.leftRel_apply] at hxy
  exact ⟨fun h => by simpa using mul_mem h <| hM hxy,
        fun h => by simpa using mul_mem h <| hM <| inv_mem hxy⟩

def decidablePred_mem_map_quotient_mk
    {R S : Type*} [CommRing R] [SetLike S R] [AddMemClass S R] (I : Ideal R)
    {M : S} (hM : (I : Set R) ⊆ M) [DecidablePred (· ∈ M)] :
    DecidablePred (· ∈ (Ideal.Quotient.mk I) '' M) := by
  have : ∀ x y, I.quotientRel x y → (x ∈ M ↔ y ∈ M) :=
    QuotientAddGroup.mem_iff_mem_of_rel _ (by simpa)
  rw [show (· ∈ (Ideal.Quotient.mk I) '' _) = (· ∈ (Quotient.mk _) '' _) by rfl,
      Quotient.image_mk_eq_lift _ this]
  exact Quotient.lift.decidablePred (· ∈ M) (by simpa)

section CommRing

variable {R : Type*} [CommRing R]

variable (R) in
open Classical in
noncomputable def IsConeLinearOrderEquiv :
    Equiv {C : Subsemiring R // C.IsCone ∧ C.HasMemOrNegMem}
          {l : LinearOrder R // IsOrderedRing R} where
  toFun := fun ⟨C, hC⟩ => have := hC.1; have := hC.2;
    ⟨.mkOfAddSubmonoid C.toAddSubmonoid, .mkOfSubsemiring C⟩
  invFun := fun ⟨_, _⟩ => ⟨.nonneg R, by simp; infer_instance, by simp; infer_instance⟩
  left_inv := fun ⟨_, _, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by ext; simp

open Classical in
@[simp]
theorem IsConeLinearOrderEquiv_apply
    (C : Subsemiring R) (h : C.IsCone ∧ C.HasMemOrNegMem) :
    (IsConeLinearOrderEquiv R ⟨C, h⟩ : LinearOrder R) =
    have := h.1; have := h.2; LinearOrder.mkOfAddSubmonoid C.toAddSubmonoid := rfl

@[simp]
theorem IsConeLinearOrderEquiv_symm_apply (l : LinearOrder R) (h : IsOrderedRing R) :
    (IsConeLinearOrderEquiv R).symm ⟨l, h⟩ = Subsemiring.nonneg R := rfl

end CommRing

section Field

variable {F : Type*} [Field F]

variable (F) in
open Classical in
noncomputable def ringOrderingLinearOrderEquiv :
    Equiv {O : Subsemiring F // O.IsOrdering}
          {l : LinearOrder F // IsStrictOrderedRing F} where
  toFun := fun ⟨O, hO⟩ =>
    let ⟨l, hl⟩ := IsConeLinearOrderEquiv F ⟨O, inferInstance, inferInstance⟩
    ⟨l, IsOrderedRing.toIsStrictOrderedRing F⟩
  invFun := fun ⟨l, hl⟩ =>
    let ⟨O, hO⟩ := (IsConeLinearOrderEquiv F).symm ⟨l, inferInstance⟩
    have := hO.1; have := hO.2; ⟨O, inferInstance⟩
  left_inv := fun ⟨_, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by ext; simp

@[simp]
theorem ringOrderingLinearOrderEquiv_apply (O : Subsemiring F) (h : O.IsOrdering) :
    (ringOrderingLinearOrderEquiv F ⟨O, h⟩ : LinearOrder F) =
    IsConeLinearOrderEquiv F ⟨O, inferInstance, inferInstance⟩ := by
  simp [ringOrderingLinearOrderEquiv]

@[simp]
theorem ringOrderingLinearOrderEquiv_symm_apply_val
    (l : LinearOrder F) (h : IsStrictOrderedRing F) :
    ((ringOrderingLinearOrderEquiv F).symm ⟨l, h⟩ : Subsemiring F) =
    (IsConeLinearOrderEquiv F).symm ⟨l, inferInstance⟩ := by
  simp [ringOrderingLinearOrderEquiv]

end Field

section Quot

variable {R : Type*} [CommRing R] (O : Subsemiring R) [O.HasMemOrNegMem]

instance : (O.map (Ideal.Quotient.mk O.support)).HasMemOrNegMem :=
  AddSubmonoid.HasMemOrNegMem.map O.toAddSubmonoid
    (f := (Ideal.Quotient.mk O.support).toAddMonoidHom) Ideal.Quotient.mk_surjective

-- TODO : move to right place
@[simp]
theorem RingHom.ker_toAddSubgroup {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
  (RingHom.ker f).toAddSubgroup = f.toAddMonoidHom.ker := by ext; simp

instance : (O.map (Ideal.Quotient.mk O.support)).IsCone where
  supportAddSubgroup_eq_bot := by
    have : (O.toAddSubmonoid.map (Ideal.Quotient.mk O.support).toAddMonoidHom).HasIdealSupport := by
      simpa using (inferInstance : (O.map (Ideal.Quotient.mk O.support)).HasIdealSupport)
    have fact : (Ideal.Quotient.mk O.support).toAddMonoidHom.ker = O.supportAddSubgroup := by
      have := Ideal.mk_ker (I := O.support)
      apply_fun Submodule.toAddSubgroup at this
      simpa [-Ideal.mk_ker, -RingHom.toAddMonoidHom_eq_coe]
    have : (Ideal.Quotient.mk O.support).toAddMonoidHom.ker ≤ O.supportAddSubgroup := by
      simp [-RingHom.toAddMonoidHom_eq_coe, fact]
    have := AddSubmonoid.map_support Ideal.Quotient.mk_surjective this
    simp [-RingHom.toAddMonoidHom_eq_coe, this]

abbrev PartialOrder.mkOfSubsemiring_quot : PartialOrder (R ⧸ O.support) :=
  .mkOfAddSubmonoid (O.map (Ideal.Quotient.mk O.support)).toAddSubmonoid

theorem IsOrderedRing.mkOfSubsemiring_quot :
    letI  _ := PartialOrder.mkOfSubsemiring_quot O
    IsOrderedRing (R ⧸ O.support) := .mkOfSubsemiring (O.map (Ideal.Quotient.mk O.support))

abbrev LinearOrder.mkOfSubsemiring_quot [DecidablePred (· ∈ O)] : LinearOrder (R ⧸ O.support) :=
  have : DecidablePred (· ∈ O.map (Ideal.Quotient.mk O.support)) := by
    simpa using decidablePred_mem_map_quotient_mk (O.support)
      (by simp [AddSubmonoid.coe_support])
  .mkOfAddSubmonoid (O.map (Ideal.Quotient.mk O.support)).toAddSubmonoid

open Classical in
noncomputable def IsConeLinearOrderEquiv_quot :
    Equiv {O : Subsemiring R // O.HasMemOrNegMem}
          (Σ I : Ideal R, {p : LinearOrder (R ⧸ I) // IsOrderedRing (R ⧸ I)}) where
  toFun := fun ⟨O, hO⟩ => ⟨O.support, ⟨.mkOfSubsemiring_quot O, .mkOfSubsemiring_quot O⟩⟩
  invFun := fun ⟨I, l, hl⟩ =>
    ⟨((IsConeLinearOrderEquiv _).symm ⟨l, hl⟩).val.comap (Ideal.Quotient.mk I),
    ⟨fun a ↦ by simpa using le_total ..⟩⟩
  left_inv := fun ⟨O, hO⟩ => by
    ext x
    simp [-Subsemiring.mem_map]
    constructor
    · simp
      intro y hy hxy
      rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, Ideal.mk_ker] at hxy
      simpa using add_mem hxy.2 hy
    · aesop
  right_inv := fun ⟨I, l, hl⟩ => by
    refine Sigma.eq ?_ ?_
    · ext; simp [AddSubmonoid.mem_support, ← ge_antisymm_iff, ← RingHom.mem_ker]
    · simp
      apply Subtype.ext
      simp
      sorry -- TODO : fix DTT hell

/- TODO : apply and symm_apply simp lemmas -/

end Quot
