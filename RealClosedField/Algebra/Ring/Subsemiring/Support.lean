/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/

import RealClosedField.Algebra.Group.Submonoid.Support
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Ring.Subsemiring.Order -- TODO : downstream

/-!
# Supports of subsemirings

Let `R` be a ring, and let `S` be a subsemiring of `R`.
If `S - S = S`, then the support of `S` forms an ideal.

## Main definitions

* `Subsemiring.support`: the support of a subsemiring, as an ideal.

-/

-- TODO : minimise duplication in proofs; ensure duplication in theorems

section Ring

variable {R : Type*} [Ring R]

namespace Subsemiring

variable (S : Subsemiring R)

@[aesop 50% apply, aesop safe forward (immediate := [hx₁])]
theorem eq_zero_of_mem_of_neg_mem [S.IsPointed] {x : R} (hx₁ : x ∈ S) (hx₂ : -x ∈ S) : x = 0 :=
  S.toAddSubmonoid.eq_zero_of_mem_of_neg_mem hx₁ hx₂

@[aesop safe forward (immediate := [hx₂])]
alias eq_zero_of_mem_of_neg_mem₂ := eq_zero_of_mem_of_neg_mem -- for Aesop

@[aesop safe forward, aesop safe apply]
theorem mem_or_neg_mem [S.IsSpanning] : ∀ a, a ∈ S ∨ -a ∈ S :=
  S.toAddSubmonoid.mem_or_neg_mem

/-- Typeclass to track when the support of a subsemiring forms an ideal. -/
class HasIdealSupport : Prop where
  smul_mem_support (x : R) {a : R} (ha : a ∈ S.support) :
    x * a ∈ S.support := by aesop

export HasIdealSupport (smul_mem_support)

variable {S} in
theorem hasIdealSupport_iff :
    S.HasIdealSupport ↔ ∀ x a : R, a ∈ S → -a ∈ S → x * a ∈ S ∧ -(x * a) ∈ S where
  mp _ := have := S.smul_mem_support; by aesop
  mpr _ := { }

section HasIdealSupport

variable [S.HasIdealSupport]

@[aesop 80% (rule_sets := [SetLike])]
theorem smul_mem (x : R) {a : R} (h₁a : a ∈ S) (h₂a : -a ∈ S) : x * a ∈ S := by
  have := S.smul_mem_support
  aesop

@[aesop 80% (rule_sets := [SetLike])]
theorem neg_smul_mem (x : R) {a : R} (h₁a : a ∈ S) (h₂a : -a ∈ S) : -(x * a) ∈ S := by
  have := S.smul_mem_support
  aesop

/-- The support `S ∩ -S` of a subsemiring `S` of a ring `R`, as an ideal. -/
def support : Ideal R where
  __ := S.toAddSubmonoid.support
  smul_mem' := by aesop

variable {S} in
@[aesop simp]
theorem mem_support {x} : x ∈ S.support ↔ x ∈ S ∧ -x ∈ S := .rfl

theorem coe_support : S.support = (S : Set R) ∩ -(S : Set R) := rfl

@[simp]
theorem toAddSubmonoid_support : S.toAddSubmonoid.support = S.support.toAddSubgroup := rfl

end HasIdealSupport

instance [S.IsSpanning] : S.HasIdealSupport where
  smul_mem_support x a ha := by
    have := S.mem_or_neg_mem x
    have : ∀ x y, -x ∈ S → -y ∈ S → x * y ∈ S := fun _ _ hx hy ↦ by simpa using mul_mem hx hy
    aesop (add 80% this)

-- PR SPLIT ↑1 ↓2

section upstream

-- TODO : move to right place and replace non-primed versions

variable {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
         (P : Subsemiring R) (Q : Subsemiring S)

@[simp]
theorem comap_toSubmonoid' : (Q.comap f).toSubmonoid = Q.toSubmonoid.comap f.toMonoidHom := by
  ext; simp

@[simp]
theorem comap_toAddSubmonoid :
    (Q.comap f).toAddSubmonoid = Q.toAddSubmonoid.comap f.toAddMonoidHom := by
  ext; simp

@[simp]
theorem map_toSubmonoid' : (P.map f).toSubmonoid = P.toSubmonoid.map f.toMonoidHom := by
  ext; simp

@[simp]
theorem map_toAddSubmonoid : (P.map f).toAddSubmonoid = P.toAddSubmonoid.map f.toAddMonoidHom := by
  ext; simp

end upstream

variable {R R' : Type*} [Ring R] [Ring R'] (f : R →+* R')
         (S T : Subsemiring R) (S' : Subsemiring R') {s : Set (Subsemiring R)}

instance [S.IsPointed] : S.HasIdealSupport where

@[simp]
theorem support_eq_bot [S.IsPointed] : S.support = ⊥ := by
  apply_fun Submodule.toAddSubgroup using Submodule.toAddSubgroup_injective
  simp [← toAddSubmonoid_support]

@[aesop simp, aesop safe forward]
theorem IsPointed.neg_one_notMem [Nontrivial R] [S.IsPointed] : -1 ∉ S := fun hc ↦ by
  simpa [S.eq_zero_of_mem_of_neg_mem (by simp) hc] using zero_ne_one' R

instance [S'.IsSpanning] : (S'.comap f).IsSpanning where

variable {f} in
theorem IsSpanning.map [S.IsSpanning] (hf : Function.Surjective f) : (S.map f).IsSpanning :=
  AddSubmonoid.IsSpanning.map S.toAddSubmonoid (f := f.toAddMonoidHom) hf

section HasIdealSupport

variable [S.HasIdealSupport] [T.HasIdealSupport] [S'.HasIdealSupport]

theorem IsPointed.of_support_eq_bot (h : S.support = ⊥) : S.IsPointed where
  eq_zero_of_mem_of_neg_mem {x} := by
    apply_fun (x ∈ ·) at h
    aesop

variable {S T} in
theorem support_mono (h : S ≤ T) : S.support ≤ T.support := fun _ ↦ by aesop

instance : (S ⊓ T).HasIdealSupport where

@[simp]
theorem support_inf : (S ⊓ T).support = S.support ⊓ T.support := by aesop

theorem HasIdealSupport.sInf (h : ∀ S ∈ s, S.HasIdealSupport) :
    (sInf s).HasIdealSupport where
  smul_mem_support := by
    simp_rw [hasIdealSupport_iff] at h -- TODO : do this properly
    aesop

@[simp]
theorem support_sInf (h : ∀ S ∈ s, S.HasIdealSupport) :
    letI _ := HasIdealSupport.sInf h
    (sInf s).support = InfSet.sInf {I | ∃ S, ∃ hS : S ∈ s, letI _ := h _ hS; I = S.support} := by
  aesop

protected theorem HasIdealSupport.sSup (hsn : s.Nonempty) (hsd : DirectedOn (· ≤ ·) s)
    (h : ∀ S ∈ s, S.HasIdealSupport) : (sSup s).HasIdealSupport := by
  simp only [hasIdealSupport_iff, mem_sSup_of_directedOn, forall_exists_index, and_imp, *] at *
  rintro x a S hS hS' T hT hT'
  rcases hsd _ hS _ hT with ⟨R, hR, hSR, hTR⟩
  have := h _ hR x a (hSR hS') (hTR hT')
  exact ⟨⟨R, hR, this.1⟩, ⟨R, hR, this.2⟩⟩

@[simp]
theorem support_sSup (hsn : s.Nonempty) (hsd : DirectedOn (· ≤ ·) s)
    (h : ∀ S ∈ s, S.HasIdealSupport) :
    letI _ : (sSup s).HasIdealSupport := HasIdealSupport.sSup hsn hsd h
    (sSup s).support = SupSet.sSup {I | ∃ S, ∃ hS : S ∈ s, letI _ := h _ hS; I = S.support} := by
  generalize_proofs
  ext x
  rw [Submodule.mem_sSup_of_directed]
  · simp only [mem_support, mem_sSup_of_directedOn, Set.mem_setOf_eq, ↓existsAndEq, true_and,
      exists_and_left, exists_prop, hsn, hsd]
    refine ⟨?_, by aesop⟩
    rintro ⟨⟨_, hx₁, _⟩, ⟨_, hx₂, _⟩⟩
    rcases hsd _ hx₁ _ hx₂ with ⟨x, _⟩
    exact ⟨x, by aesop⟩
  · rcases hsn with ⟨S, hS⟩
    exact ⟨let _ := h S hS; S.support, by aesop⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rcases hsd _ hx _ hy with ⟨z, hz, _, _⟩
    let _ := h _ hx
    let _ := h _ hy
    let _ := h _ hz
    exact ⟨z.support, by aesop (add safe apply support_mono)⟩

instance : (S'.comap f).HasIdealSupport where
  smul_mem_support x a ha := by simpa using smul_mem_support (f x) (by simpa using ha)

@[simp]
theorem comap_support : (S'.comap f).support = (S'.support).comap f := by
  ext x
  have := S'.toAddSubmonoid.comap_support f.toAddMonoidHom
  apply_fun (x ∈ ·) at this
  simpa [-AddSubmonoid.comap_support]

variable {f S} in
theorem HasIdealSupport.map (hf : Function.Surjective f)
    (hsupp : f.toAddMonoidHom.ker ≤ S.toAddSubmonoid.support) :
    HasIdealSupport (S.map f) where
  smul_mem_support x a ha := by
    rw [map_toAddSubmonoid, AddSubmonoid.map_support hsupp] at ha
    rcases ha with ⟨a', ha', rfl⟩
    rcases hf x with ⟨x', rfl⟩
    have := smul_mem_support x' ha'
    aesop

variable {f S} in
@[simp]
theorem map_support (hf : Function.Surjective f) (hsupp : RingHom.ker f ≤ S.support) :
    letI _ := HasIdealSupport.map hf hsupp
    (S.map f).support = (S.support).map f := by
  ext x
  have := AddSubmonoid.map_support (f := f.toAddMonoidHom) hsupp
  apply_fun (x ∈ ·) at this
  simpa [Ideal.mem_map_iff_of_surjective f hf]

end HasIdealSupport

end Subsemiring

section downstream

-- TODO : downstream to `Mathlib.Algebra.Ring.Subsemiring.Order` or further

variable (R : Type*) [Ring R]

instance [LinearOrder R] [IsOrderedRing R] : (Subsemiring.nonneg R).IsSpanning :=
  inferInstanceAs (AddSubmonoid.nonneg R).IsSpanning

instance [PartialOrder R] [IsOrderedRing R] : (Subsemiring.nonneg R).IsPointed :=
  inferInstanceAs (AddSubmonoid.nonneg R).IsPointed

variable {R} (S : Subsemiring R) [S.IsPointed]

theorem IsOrderedRing.mkOfSubsemiring :
    letI _ := PartialOrder.mkOfAddSubmonoid S.toAddSubmonoid
    IsOrderedRing R :=
  letI _ := PartialOrder.mkOfAddSubmonoid S.toAddSubmonoid
  haveI := IsOrderedAddMonoid.mkOfAddSubmonoid S.toAddSubmonoid
  haveI : ZeroLEOneClass R := ⟨by simp⟩
  .of_mul_nonneg fun x y xnn ynn ↦ show _ ∈ S by simpa using Subsemiring.mul_mem _ xnn ynn

namespace Ring

variable (R) in
/-- Equivalence between subsemirings with zero support in a ring `R`
    and partially ordered ring structures on `R`. -/
noncomputable def isPointedPartialOrderEquiv :
    Equiv {C : Subsemiring R // C.IsPointed}
          {o : PartialOrder R // IsOrderedRing R} where
  toFun := fun ⟨C, _⟩ => ⟨.mkOfAddSubmonoid C.toAddSubmonoid, .mkOfSubsemiring _⟩
  invFun := fun ⟨_, _⟩ => ⟨.nonneg R, inferInstance⟩
  left_inv := fun ⟨_, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by ext; simp

@[simp]
theorem isPointedPartialOrderEquiv_apply
    (C : Subsemiring R) (h : C.IsPointed) :
    isPointedPartialOrderEquiv R ⟨C, h⟩ = PartialOrder.mkOfAddSubmonoid C.toAddSubmonoid := rfl

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
  toFun := fun ⟨C, hC⟩ => have := hC.1; have := hC.2;
    ⟨.mkOfAddSubmonoid C.toAddSubmonoid, .mkOfSubsemiring C⟩
  invFun := fun ⟨_, _⟩ => ⟨.nonneg R, by infer_instance, by infer_instance⟩
  left_inv := fun ⟨_, _, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by ext; simp

open Classical in
@[simp]
theorem isPointedLinearOrderEquiv_apply
    (C : Subsemiring R) (h : C.IsPointed ∧ C.IsSpanning) :
    isPointedLinearOrderEquiv R ⟨C, h⟩ =
    have := h.1; have := h.2; LinearOrder.mkOfAddSubmonoid C.toAddSubmonoid := rfl

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

variable {R : Type*} [CommRing R] (O : Subsemiring R) [O.IsSpanning]

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
