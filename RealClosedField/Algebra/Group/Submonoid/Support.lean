/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.RingTheory.Ideal.Maps

/-!
# Supports of submonoids

Let `G` be an (additive) group, and let `M` be a submonoid of `G`.
The *support* of `M` is `M ∩ -M`, the largest subgroup of `M`.
When `M ∪ -M = G`, the support of `M` forms an ideal.
We define supports and prove how they interact with operations.

## Main definitions

* `AddSubmonoid.supportAddSubgroup`: the support of a submonoid as a subgroup.
* `AddSubmonoid.support`: the support of a submonoid as an ideal.
* `AddSubmonoid.HasMemOrNegMem`: typeclass for submonoids satisfying `M ∪ -M = G`.

-/

namespace AddSubmonoid

variable {G : Type*} [AddGroup G] (M : AddSubmonoid G)

/-- Typeclass for submonoids `M` of a group `G` such that `M ∪ -M = G`. -/
class HasMemOrNegMem (M : AddSubmonoid G) : Prop where
  mem_or_neg_mem (M) (a : G) : a ∈ M ∨ -a ∈ M := by aesop

export HasMemOrNegMem (mem_or_neg_mem)

attribute [aesop safe forward] mem_or_neg_mem

end AddSubmonoid

namespace Submonoid

variable {G : Type*} [Group G] (M : Submonoid G)

/-- Typeclass for submonoids `M` of a group `G` such that `M ∪ -M = G`. -/
@[to_additive]
class HasMemOrInvMem {G : Type*} [Group G] (M : Submonoid G) : Prop where
  mem_or_inv_mem (M) (a : G) : a ∈ M ∨ a⁻¹ ∈ M := by aesop

export HasMemOrInvMem (mem_or_inv_mem)

attribute [aesop safe forward] mem_or_inv_mem

@[to_additive]
theorem HasMemOrInvMem.of_le {M N : Submonoid G} [M.HasMemOrInvMem] (h : M ≤ N) :
    N.HasMemOrInvMem where
  mem_or_inv_mem a := by aesop

/--
The support of a submonoid `M` of a group `G` is `M ∩ M⁻¹`,
the largest subgroup contained in `M`.
-/
@[to_additive
/-- The support of a submonoid `M` of a group `G` is `M ∩ -M`,
the largest subgroup contained in `M`. -/]
def supportSubgroup : Subgroup G where
  carrier := M ∩ M⁻¹
  one_mem' := by aesop
  mul_mem' := by aesop
  inv_mem' := by aesop

variable {M} in
@[to_additive (attr := aesop simp)]
theorem mem_supportSubgroup {x} : x ∈ M.supportSubgroup ↔ x ∈ M ∧ x⁻¹ ∈ M := .rfl

@[to_additive]
theorem coe_supportSubgroup : M.supportSubgroup = (M ∩ M⁻¹ : Set G) := rfl

end Submonoid

section Ring

variable {R : Type*} [Ring R]

namespace AddSubmonoid

variable (M : AddSubmonoid R)

/-- Typeclass to track when the support of a submonoid forms an ideal. -/
class HasIdealSupport : Prop where
  smul_mem_support (x : R) {a : R} (ha : a ∈ M.supportAddSubgroup) :
    x * a ∈ M.supportAddSubgroup := by aesop

export HasIdealSupport (smul_mem_support)

variable {M} in
theorem hasIdealSupport_iff :
    M.HasIdealSupport ↔ ∀ x a : R, a ∈ M → -a ∈ M → x * a ∈ M ∧ -(x * a) ∈ M where
  mp _ := have := M.smul_mem_support; by aesop
  mpr _ := { }

section HasIdealSupport

variable [M.HasIdealSupport]

@[aesop 80% (rule_sets := [SetLike])]
theorem smul_mem (x : R) {a : R} (h₁a : a ∈ M) (h₂a : -a ∈ M) : x * a ∈ M := by
  have := M.smul_mem_support
  aesop

@[aesop 80% (rule_sets := [SetLike])]
theorem neg_smul_mem (x : R) {a : R} (h₁a : a ∈ M) (h₂a : -a ∈ M) : -(x * a) ∈ M := by
  have := M.smul_mem_support
  aesop

/-- The support `M ∩ -M` of a submonoid `M` of a ring `R`, as an ideal. -/
def support : Ideal R where
  __ := supportAddSubgroup M
  smul_mem' := by aesop

variable {M} in
@[aesop simp]
theorem mem_support {x} : x ∈ M.support ↔ x ∈ M ∧ -x ∈ M := .rfl

theorem coe_support : M.support = (M : Set R) ∩ -(M : Set R) := rfl

@[simp]
theorem supportAddSubgroup_eq : M.supportAddSubgroup = M.support.toAddSubgroup := rfl

end HasIdealSupport

end AddSubmonoid

namespace Subsemiring

instance (M : Subsemiring R) [M.HasMemOrNegMem] : M.HasIdealSupport where
  smul_mem_support x a ha := by
    have := M.mem_or_neg_mem x
    have : ∀ x y, -x ∈ M → -y ∈ M → x * y ∈ M := fun _ _ hx hy ↦ by simpa using mul_mem hx hy
    aesop (add 80% this)

end Subsemiring

end Ring

-- PR SPLIT ↑1 ↓2

-- TODO : move to right place and replace non-primed versions
namespace Subsemiring

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

end Subsemiring

namespace Submonoid

section Group

variable {G H : Type*} [Group G] [Group H] (f : G →* H) (M N : Submonoid G) (M' : Submonoid H)

variable {M N} in
@[to_additive]
theorem supportSubgroup_mono (h : M ≤ N) : M.supportSubgroup ≤ N.supportSubgroup :=
  fun _ ↦ by aesop

@[to_additive (attr := simp)]
theorem supportSubgroup_inf : (M ⊓ N).supportSubgroup = M.supportSubgroup ⊓ N.supportSubgroup := by
  aesop

@[to_additive (attr := simp)]
theorem supportSubgroup_sInf (s : Set (Submonoid G)) :
    (sInf s).supportSubgroup = InfSet.sInf (supportSubgroup '' s) := by
  ext
  aesop

@[to_additive]
instance [M'.HasMemOrInvMem] : (M'.comap f).HasMemOrInvMem where
  mem_or_inv_mem x := have := M'.mem_or_inv_mem; by aesop

@[to_additive (attr := simp)]
theorem comap_supportSubgroup : (M'.comap f).supportSubgroup = (M'.supportSubgroup).comap f := by
  ext; aesop

variable {f} in
@[to_additive]
theorem HasMemOrNegMem.map [M.HasMemOrInvMem] (hf : Function.Surjective f) :
    (M.map f).HasMemOrInvMem where
  mem_or_inv_mem x := by
    obtain ⟨x', rfl⟩ := hf x
    aesop

end Group

section CommGroup

variable {G H : Type*} [CommGroup G] [CommGroup H] (f : G →* H) (M : Submonoid G)

variable {f M} in
@[to_additive (attr := simp)]
theorem map_supportSubgroup
    (hsupp : f.ker ≤ M.supportSubgroup) :
    (M.map f).supportSubgroup = (M.supportSubgroup).map f := by
  ext
  refine ⟨fun ⟨⟨a, ⟨ha₁, ha₂⟩⟩, ⟨b, ⟨hb₁, hb₂⟩⟩⟩ => ?_, by aesop⟩
  have : (a * b)⁻¹ * b ∈ M := by exact mul_mem (hsupp (show f (a * b) = 1 by simp_all)).2 hb₁
  aesop

end CommGroup

end Submonoid

namespace AddSubmonoid

section Ring

variable {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (M N : AddSubmonoid R) (M' : AddSubmonoid S)
         {s : Set (AddSubmonoid R)}

section HasIdealSupport

variable [M.HasIdealSupport] [N.HasIdealSupport] [M'.HasIdealSupport]

variable {M N} in
theorem support_mono (h : M ≤ N) :support M ≤ support N := fun _ ↦ by aesop

instance : (M ⊓ N).HasIdealSupport where

@[simp]
theorem support_inf : (M ⊓ N).support = M.support ⊓ N.support := by
  apply_fun Submodule.toAddSubgroup using Submodule.toAddSubgroup_injective
  simpa [-Submodule.toAddSubgroup_inj] using supportAddSubgroup_inf (M := M) (N := N)

theorem HasIdealSupport.sInf (h : ∀ M ∈ s, M.HasIdealSupport) :
    (sInf s).HasIdealSupport where
  smul_mem_support := by
    simp_rw [hasIdealSupport_iff] at h -- TODO : do this properly
    aesop

@[simp]
theorem support_sInf (h : ∀ M ∈ s, M.HasIdealSupport) :
    letI _ := HasIdealSupport.sInf h
    (sInf s).support = InfSet.sInf {I | ∃ M, ∃ hM : M ∈ s, letI _ := h _ hM; I = M.support} := by
  aesop

@[simp]
theorem supportAddSubgroup_sSup (hsn : s.Nonempty) (hsd : DirectedOn (· ≤ ·) s) :
    (sSup s).supportAddSubgroup = SupSet.sSup (supportAddSubgroup '' s) := by
  ext x
  rw [AddSubgroup.mem_sSup_of_directedOn (by simp_all)
       (.mono_comp (fun _ _ h ↦ supportAddSubgroup_mono h) hsd)]
  simp only [mem_supportAddSubgroup, mem_sSup_of_directedOn, Set.mem_image,
    exists_exists_and_eq_and, hsd, hsn]
  refine ⟨?_, by aesop⟩
  rintro ⟨⟨_, hx₁, _⟩, ⟨_, hx₂, _⟩⟩
  rcases hsd _ hx₁ _ hx₂ with ⟨x, _⟩
  exact ⟨x, by aesop⟩

protected theorem HasIdealSupport.sSup (hsn : s.Nonempty) (hsd : DirectedOn (· ≤ ·) s)
    (h : ∀ M ∈ s, M.HasIdealSupport) : (sSup s).HasIdealSupport := by
  simp only [hasIdealSupport_iff, mem_sSup_of_directedOn, forall_exists_index, and_imp, *] at *
  rintro x a M hM hM' N hN hN'
  rcases hsd _ hM _ hN with ⟨R, hR, hMR, hNR⟩
  have := h _ hR x a (hMR hM') (hNR hN')
  exact ⟨⟨R, hR, this.1⟩, ⟨R, hR, this.2⟩⟩

@[simp]
theorem support_sSup (hsn : s.Nonempty) (hsd : DirectedOn (· ≤ ·) s)
    (h : ∀ M ∈ s, M.HasIdealSupport) :
    letI _ : (sSup s).HasIdealSupport := HasIdealSupport.sSup hsn hsd h
    (sSup s).support = SupSet.sSup {I | ∃ M, ∃ hM : M ∈ s, letI _ := h _ hM; I = M.support} := by
  generalize_proofs
  ext x
  have : x ∈ (sSup s).support ↔ x ∈ SupSet.sSup (supportAddSubgroup '' s) := by
    simp [← supportAddSubgroup_sSup hsn hsd]
  rw [this,
      AddSubgroup.mem_sSup_of_directedOn (by simp_all)
        (.mono_comp (fun _ _ h ↦ supportAddSubgroup_mono h) hsd),
      Submodule.mem_sSup_of_directed]
  · aesop
  · rcases hsn with ⟨M, hM⟩
    exact ⟨let _ := h M hM; M.support, by aesop⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rcases hsd _ hx _ hy with ⟨z, hz, _, _⟩
    let _ := h _ hx
    let _ := h _ hy
    let _ := h _ hz
    exact ⟨z.support, by aesop (add safe apply support_mono)⟩

instance : (M'.comap f.toAddMonoidHom).HasIdealSupport where
  smul_mem_support x a ha := by simpa using smul_mem_support (f x) (by simpa using ha)

@[simp]
theorem comap_support : (M'.comap f.toAddMonoidHom).support = (M'.support).comap f := by
  ext x
  have := M'.comap_supportAddSubgroup f.toAddMonoidHom
  apply_fun (x ∈ ·) at this
  simpa [-RingHom.toAddMonoidHom_eq_coe]

variable {f M} in
theorem HasIdealSupport.map (hf : Function.Surjective f)
    (hsupp : f.toAddMonoidHom.ker ≤ M.supportAddSubgroup) :
    HasIdealSupport (M.map f.toAddMonoidHom) where
  smul_mem_support x a ha := by
    rw [map_supportAddSubgroup hsupp] at ha
    rcases ha with ⟨a', ha', rfl⟩
    rcases hf x with ⟨x', rfl⟩
    have := smul_mem_support x' ha'
    aesop (erase simp RingHom.toAddMonoidHom_eq_coe)

end HasIdealSupport

end Ring

section CommRing

variable {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (M : AddSubmonoid R) [M.HasIdealSupport]

variable {f M} in
@[simp]
theorem map_support (hf : Function.Surjective f)
    (hsupp : f.toAddMonoidHom.ker ≤ M.supportAddSubgroup) :
    letI _ := HasIdealSupport.map hf hsupp
    (M.map f.toAddMonoidHom).support = (M.support).map f := by
  ext x
  have := map_supportAddSubgroup hsupp
  apply_fun (x ∈ ·) at this
  simpa [Ideal.mem_map_iff_of_surjective f hf]

end CommRing

end AddSubmonoid
