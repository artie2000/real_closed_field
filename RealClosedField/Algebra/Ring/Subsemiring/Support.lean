/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/

import RealClosedField.Algebra.Group.Submonoid.Support
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Ring.Subsemiring.Order -- TODO : downstream

/-!
# Supports of subsemirings

Let `R` be a ring, and let `S` be a subsemiring of `R`.
If `S` generates `R` as a subring, then the support of `S` forms an ideal.

## Main definitions

* `Subsemiring.support`: the support of a subsemiring, as an ideal.

-/

variable {R : Type*} [Ring R]

namespace Subsemiring

variable {S : Subsemiring R}

@[aesop safe forward (immediate := [hS, hx₁])]
theorem eq_zero_of_mem_of_neg_mem (hS : S.IsPointed) {x : R}
    (hx₁ : x ∈ S) (hx₂ : -x ∈ S) : x = 0 := hS.eq_zero_of_mem_of_neg_mem hx₁ hx₂

@[aesop safe forward (immediate := [hS, hx₂])]
alias eq_zero_of_mem_of_neg_mem₂ := eq_zero_of_mem_of_neg_mem -- for Aesop

@[aesop safe forward]
theorem mem_or_neg_mem (hS : S.IsSpanning) : ∀ a, a ∈ S ∨ -a ∈ S :=
  hS.mem_or_neg_mem

@[aesop simp, aesop safe forward]
theorem _root_.AddSubmonoid.IsPointed.neg_one_notMem [Nontrivial R]
    (hS : S.IsPointed) : -1 ∉ S := fun hc ↦ by
  simpa [S.eq_zero_of_mem_of_neg_mem hS (by simp) hc] using zero_ne_one' R

-- PR SPLIT ↑1 ↓2

-- TODO : minimise duplication in proofs; ensure duplication in theorems

section upstream

-- TODO : move to right place and replace non-primed versions

variable {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
         (P : Subsemiring R) (Q : Subsemiring S)


--  existing `comap_toSubmonoid` had RHS in a bad form for `simp` - `Submonoid.mem_mk` doesn't work
@[simp]
theorem comap_toSubmonoid' : (Q.comap f).toSubmonoid = Q.toSubmonoid.comap f.toMonoidHom := by
  ext; simp [-comap_toSubmonoid]

@[simp]
theorem comap_toAddSubmonoid :
    (Q.comap f).toAddSubmonoid = Q.toAddSubmonoid.comap f.toAddMonoidHom := by
  ext; simp

-- existing `map_toSubmonoid` had RHS in a bad form for `simp` - `Submonoid.mem_mk` doesn't work
@[simp]
theorem map_toSubmonoid' : (P.map f).toSubmonoid = P.toSubmonoid.map f.toMonoidHom := by
  ext; simp [-map_toSubmonoid]

@[simp]
theorem map_toAddSubmonoid : (P.map f).toAddSubmonoid = P.toAddSubmonoid.map f.toAddMonoidHom := by
  ext; simp

end upstream

variable {R R' : Type*} [Ring R] [Ring R'] {f : R →+* R'}
         {S T : Subsemiring R} {S' : Subsemiring R'} {s : Set (Subsemiring R)}

variable (f) in
theorem isSpanning_comap (hS' : S'.IsSpanning) : (S'.comap f).IsSpanning :=
  hS'.comap f.toAddMonoidHom

theorem isSpanning_map (hS : S.IsSpanning) (hf : Function.Surjective f) : (S.map f).IsSpanning :=
  hS.map (f := f.toAddMonoidHom) hf

end Subsemiring

section downstream

-- TODO : downstream to `Mathlib.Algebra.Ring.Subsemiring.Order` or further

variable (R : Type*) [Ring R]

theorem Subsemiring.nonneg.isPointed [PartialOrder R] [IsOrderedRing R] :
    (Subsemiring.nonneg R).IsPointed := AddSubmonoid.nonneg.isPointed R

theorem Subsemiring.nonneg.isSpanning [LinearOrder R] [IsOrderedRing R] :
    (Subsemiring.nonneg R).IsSpanning := AddSubmonoid.nonneg.isSpanning R

variable {R} {S : Subsemiring R} (hS : S.IsPointed)

theorem IsOrderedRing.mkOfSubsemiring :
    letI _ := PartialOrder.mkOfAddSubmonoid hS
    IsOrderedRing R :=
  letI _ := PartialOrder.mkOfAddSubmonoid hS
  haveI := IsOrderedAddMonoid.mkOfAddSubmonoid hS
  haveI : ZeroLEOneClass R := ⟨by simp⟩
  .of_mul_nonneg fun x y xnn ynn ↦ show _ ∈ S by simpa using Subsemiring.mul_mem _ xnn ynn

namespace Ring

variable (R) in
/-- Equivalence between subsemirings with zero support in a ring `R`
    and partially ordered ring structures on `R`. -/
noncomputable def isPointedPartialOrderEquiv :
    Equiv {C : Subsemiring R // C.IsPointed}
          {o : PartialOrder R // IsOrderedRing R} where
  toFun := fun ⟨_, hC⟩ => ⟨.mkOfAddSubmonoid hC, .mkOfSubsemiring _⟩
  invFun := fun ⟨_, _⟩ => ⟨.nonneg R, Subsemiring.nonneg.isPointed R⟩
  left_inv := fun ⟨_, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by ext; simp [LE.le]

@[simp]
theorem isPointedPartialOrderEquiv_apply
    (C : Subsemiring R) (h : C.IsPointed) :
    isPointedPartialOrderEquiv R ⟨C, h⟩ = PartialOrder.mkOfAddSubmonoid h := rfl

@[simp]
theorem isPointedPartialOrderEquiv_symm_apply (o : PartialOrder R) (h : IsOrderedRing R) :
    (isPointedPartialOrderEquiv R).symm ⟨o, h⟩ = Subsemiring.nonneg R := rfl

variable (R) in
open Classical in
/-- Equivalence between maximal subsemirings with zero support in a ring `R`
    and linearly ordered ring structures on `R`. -/
noncomputable def isPointedLinearOrderEquiv :
    Equiv {C : Subsemiring R // C.IsPointed ∧ C.IsSpanning}
          {o : LinearOrder R // IsOrderedRing R} where
  toFun := fun ⟨C, hC⟩ => ⟨.mkOfAddSubmonoid hC.1 hC.2, .mkOfSubsemiring hC.1⟩
  invFun := fun ⟨_, _⟩ =>
    ⟨.nonneg R, Subsemiring.nonneg.isPointed R, Subsemiring.nonneg.isSpanning R⟩
  left_inv := fun ⟨_, _, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by ext; simp

open Classical in
@[simp]
theorem isPointedLinearOrderEquiv_apply
    (C : Subsemiring R) (h : C.IsPointed ∧ C.IsSpanning) :
    isPointedLinearOrderEquiv R ⟨C, h⟩ = LinearOrder.mkOfAddSubmonoid h.1 h.2 := rfl

@[simp]
theorem isPointedLinearOrderEquiv_symm_apply (o : LinearOrder R) (h : IsOrderedRing R) :
    (isPointedLinearOrderEquiv R).symm ⟨o, h⟩ = Subsemiring.nonneg R := rfl

end Ring

/- TODO : quotient versions: need to lift the constructions to prop equality?

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

-- end upstream

section Quot

-- TODO : group and partial versions

variable {R : Type*} [CommRing R] (O : Subsemiring R) (hO : O.IsSpanning)

instance : (O.map (Ideal.Quotient.mk O.support)).IsSpanning :=
  AddSubmonoid.IsSpanning.map O.toAddSubmonoid
    (f := (Ideal.Quotient.mk O.support).toAddMonoidHom) Ideal.Quotient.mk_surjective

-- TODO : move to right place
@[simp]
theorem RingHom.ker_toAddSubgroup {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
  (RingHom.ker f).toAddSubgroup = f.toAddMonoidHom.ker := by ext; simp

-- TODO : make proof less awful
instance : (O.map (Ideal.Quotient.mk O.support)).IsPointed where
  supportAddSubgroup_eq_bot := by
    have : (O.toAddSubmonoid.map (Ideal.Quotient.mk O.support).toAddMonoidHom).HasIdealSupport := by
      simpa using inferInstanceAs (O.map (Ideal.Quotient.mk O.support)).HasIdealSupport
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

-- TODO : come up with correct statement and name
open Classical in
noncomputable def subsemiringLinearOrderEquiv (I : Ideal R) :
    Equiv {O : Subsemiring R // ∃ _ : O.IsSpanning, O.support = I}
          {o : LinearOrder (R ⧸ I) // IsOrderedRing (R ⧸ I)} where
  toFun := fun ⟨O, hO⟩ => have := hO.1; have hs := hO.2; ⟨by rw [← hs]; exact .mkOfSubsemiring_quot O, .mkOfSubsemiring_quot O⟩
  invFun := fun ⟨o, ho⟩ =>
    ⟨((Ring.isPointedLinearOrderEquiv _).symm ⟨o, ho⟩).val.comap (Ideal.Quotient.mk I),
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

-/

end downstream
