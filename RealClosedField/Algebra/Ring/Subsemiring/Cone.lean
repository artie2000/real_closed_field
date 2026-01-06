/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/

import RealClosedField.Algebra.Group.Submonoid.Cone
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
theorem eq_zero_of_mem_of_neg_mem [S.IsStrictCone] {x : R} (hx₁ : x ∈ S) (hx₂ : -x ∈ S) : x = 0 :=
  S.toAddSubmonoid.eq_zero_of_mem_of_neg_mem hx₁ hx₂

@[aesop safe forward (immediate := [hx₂])]
alias eq_zero_of_mem_of_neg_mem₂ := eq_zero_of_mem_of_neg_mem -- for Aesop

@[aesop safe forward, aesop safe apply]
theorem mem_or_neg_mem [S.IsGeneratingCone] : ∀ a, a ∈ S ∨ -a ∈ S :=
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

/-- The support `S ∩ -S` of a submonoid `S` of a ring `R`, as an ideal. -/
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

instance (S : Subsemiring R) [S.IsGeneratingCone] : S.HasIdealSupport where
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

section Ring

variable {R R' : Type*} [Ring R] [Ring R'] (f : R →+* R')
         (S T : Subsemiring R) (S' : Subsemiring R') {s : Set (Subsemiring R)}

instance [S.IsStrictCone] : S.HasIdealSupport where

@[simp]
theorem support_eq_bot [S.IsStrictCone] : S.support = ⊥ := by
  apply_fun Submodule.toAddSubgroup using Submodule.toAddSubgroup_injective
  simp [← toAddSubmonoid_support]

@[aesop simp, aesop safe forward]
theorem IsStrictCone.neg_one_notMem [Nontrivial R] [S.IsStrictCone] : -1 ∉ S := fun hc ↦ by
  simpa [S.eq_zero_of_mem_of_neg_mem (by simp) hc] using zero_ne_one' R

section HasIdealSupport

variable [S.HasIdealSupport] [T.HasIdealSupport] [S'.HasIdealSupport]

theorem IsStrictCone.of_support_eq_bot (h : S.support = ⊥) : S.IsStrictCone where
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
  have : x ∈ (sSup s).support ↔ x ∈ SupSet.sSup (support '' s) := by
    simp [← support_sSup hsn hsd]
  rw [this,
      AddSubgroup.mem_sSup_of_directedOn (by simp_all)
        (.mono_comp (fun _ _ h ↦ support_mono h) hsd),
      Submodule.mem_sSup_of_directed]
  · aesop
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
  simpa [-RingHom.toAddMonoidHom_eq_coe]

variable {f S} in
theorem HasIdealSupport.map (hf : Function.Surjective f)
    (hsupp : f.toAddMonoidHom.ker ≤ S.toAddSubmonoid.support) :
    HasIdealSupport (S.map f) where
  smul_mem_support x a ha := by
    rw [AddSubmonoid.map_support hsupp] at ha
    rcases ha with ⟨a', ha', rfl⟩
    rcases hf x with ⟨x', rfl⟩
    have := smul_mem_support x' ha'
    aesop (erase simp RingHom.toAddMonoidHom_eq_coe)

end HasIdealSupport

end Ring

section CommRing

variable {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (S : Subsemiring R) [S.HasIdealSupport]

variable {f S} in
@[simp]
theorem map_support (hf : Function.Surjective f) (hsupp : RingHom.ker f ≤ S.support) :
    letI _ := HasIdealSupport.map hf hsupp
    (S.map f).support = (S.support).map f := by
  ext x
  have := AddSubmonoid.map_support (f := f.toAddMonoidHom) hsupp
  apply_fun (x ∈ ·) at this
  simpa [Ideal.mem_map_iff_of_surjective f hf]

end CommRing

section downstream

-- TODO : downstream to `Mathlib.Algebra.Ring.Subsemiring.Order` or further

variable {R : Type*} [Ring R] (C : Subsemiring R)

instance [LinearOrder R] [IsOrderedRing R] : (nonneg R).IsGeneratingCone :=
  (inferInstance : (AddSubmonoid.nonneg R).IsGeneratingCone)

instance [PartialOrder R] [IsOrderedRing R] : (nonneg R).IsStrictCone :=
  (inferInstance : (AddSubmonoid.nonneg R).IsStrictCone)

end downstream

end Subsemiring
