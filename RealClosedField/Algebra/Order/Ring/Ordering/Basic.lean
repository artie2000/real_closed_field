
/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import RealClosedField.Algebra.Order.Ring.Ordering.Defs
import RealClosedField.Algebra.Ring.Semireal.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!

We prove basic properties of (pre)orderings on rings and their supports,
and define standard operations on them.

Note that the "preordering closure" of a set does not exist in general. The theory of
extending preorderings is given in `Algebra.Order.Ring.Ordering.Adjoin`.

## References

- [*An introduction to real algebra*, T.Y. Lam][lam_1984]

-/

namespace Submonoid

variable {G H : Type} [Group G] [Group H] (f : G →* H) (S T : Submonoid G) (S' : Submonoid H)

variable {S T} in
@[to_additive]
theorem supportSubgroup_mono (h : S ≤ T) : S.supportSubgroup ≤ T.supportSubgroup :=
  fun _ ↦ by aesop (add simp mem_supportSubgroup)

@[to_additive (attr := simp)]
theorem supportSubgroup_inf : (S ⊓ T).supportSubgroup = S.supportSubgroup ⊓ T.supportSubgroup := by
  aesop (add simp mem_supportSubgroup)

@[to_additive (attr := simp)]
theorem supportSubgroup_sInf (s : Set (Submonoid G)) :
    (sInf s).supportSubgroup = InfSet.sInf (supportSubgroup '' s) := by
  ext
  aesop (add simp mem_supportSubgroup, simp mem_sInf)

@[to_additive]
instance [S'.HasMemOrInvMem'] : (S'.comap f).HasMemOrInvMem' where
  mem_or_inv_mem x := by simpa using S'.mem_or_inv_mem (f x)

@[to_additive (attr := simp)]
theorem comap_supportSubgroup : (S'.comap f).supportSubgroup = (S'.supportSubgroup).comap f := by
  ext; simp [mem_supportSubgroup]

variable {f} in
@[to_additive]
theorem HasMemOrNegMem.map [S.HasMemOrInvMem'] (hf : Function.Surjective f) :
    (S.map f).HasMemOrInvMem' where
  mem_or_inv_mem x := by
    obtain ⟨x', rfl⟩ := hf x
    have := S.mem_or_inv_mem x'
    aesop


--TODO : comm
variable {f S} in
@[to_additive (attr := simp)]
theorem map_supportSubgroup
    (hsupp : (f.ker : Set G) ⊆ S.supportSubgroup) :
    (S.map f).supportSubgroup = (S.supportSubgroup).map f := by
  ext
  refine ⟨fun ⟨⟨a, ⟨ha₁, ha₂⟩⟩, ⟨b, ⟨hb₁, hb₂⟩⟩⟩ => ?_, by aesop (add simp mem_supportSubgroup)⟩
  have : (a * b)⁻¹ * b ∈ S := by exact mul_mem (hsupp (show f (a * b) = 1 by simp_all)).2 hb₁
  aesop (add simp mem_supportSubgroup)

end Submonoid

namespace AddSubmonoid

variable {R S : Type} [Ring R] [Ring S] (f : R →+* S) (P Q : AddSubmonoid R) (P' : AddSubmonoid S)
         [P.HasIdealSupport] [Q.HasIdealSupport] [P'.HasIdealSupport]

variable {P Q} in
theorem support_mono (h : P ≤ Q) :support P ≤ support Q := fun _ ↦ by aesop (add simp mem_support)

theorem HasIdealSupport.smul_mem (x : R) {a : R} (h₁a : a ∈ P) (h₂a : -a ∈ P) : x * a ∈ P := by
  grind [hasIdealSupport_iff]

theorem HasIdealSupport.neg_smul_mem (x : R) {a : R} (h₁a : a ∈ P) (h₂a : -a ∈ P) :
    -(x * a) ∈ P := by
  grind [hasIdealSupport_iff]

instance : (P ⊓ Q).HasIdealSupport := by simp_all [hasIdealSupport_iff]

@[simp]
theorem support_inf : (P ⊓ Q).support = P.support ⊓ Q.support := by
  apply_fun Submodule.toAddSubgroup using Submodule.toAddSubgroup_injective
  simpa [-Submodule.toAddSubgroup_inj] using supportAddSubgroup_inf (S := P) (T := Q)

theorem HasIdealSupport.sInf {S : Set (AddSubmonoid R)} (h : ∀ P ∈ S, P.HasIdealSupport) :
    (sInf S).HasIdealSupport := by
  simp_all [hasIdealSupport_iff, mem_sInf]

@[simp]
theorem support_sInf {S : Set (AddSubmonoid R)} (h : ∀ P ∈ S, P.HasIdealSupport) :
    letI _ := HasIdealSupport.sInf h
    (sInf S).support = InfSet.sInf {s | ∃ P, ∃ hP : P ∈ S, letI _ := h _ hP; s = P.support} := by
  aesop (add simp mem_support, simp mem_sInf)

@[simp]
theorem supportAddSubgroup_sSup {S : Set (AddSubmonoid R)}
    (hSn : S.Nonempty) (hSd : DirectedOn (· ≤ ·) S) :
    (sSup S).supportAddSubgroup = SupSet.sSup (supportAddSubgroup '' S) := by
  ext x
  rw [AddSubgroup.mem_sSup_of_directedOn (by simp_all)
       (.mono_comp (fun _ _ h ↦ supportAddSubgroup_mono h) hSd)]
  simp only [mem_supportAddSubgroup, mem_sSup_of_directedOn, Set.mem_image,
    exists_exists_and_eq_and, hSd, hSn]
  refine ⟨?_, by aesop⟩
  rintro ⟨⟨_, hs₁, _⟩, ⟨_, hs₂, _⟩⟩
  rcases hSd _ hs₁ _ hs₂ with ⟨s, hs⟩
  exact ⟨s, by aesop⟩

protected theorem HasIdealSupport.sSup {S : Set (AddSubmonoid R)}
    (hSn : S.Nonempty) (hSd : DirectedOn (· ≤ ·) S)
    (h : ∀ P ∈ S, P.HasIdealSupport) : (sSup S).HasIdealSupport := by
  simp only [hasIdealSupport_iff, mem_sSup_of_directedOn, forall_exists_index, and_imp, *] at *
  rintro x a P hP hP' Q hQ hQ'
  rcases hSd _ hP _ hQ with ⟨R, hR, hPR, hQR⟩
  have := h _ hR x a (hPR hP') (hQR hQ')
  exact ⟨⟨R, hR, this.1⟩, ⟨R, hR, this.2⟩⟩

@[simp]
theorem support_sSup {S : Set (AddSubmonoid R)} (hSn : S.Nonempty) (hSd : DirectedOn (· ≤ ·) S)
    (h : ∀ P ∈ S, P.HasIdealSupport) :
    letI _ : (sSup S).HasIdealSupport := HasIdealSupport.sSup hSn hSd h
    (sSup S).support = SupSet.sSup {s | ∃ P, ∃ hP : P ∈ S, letI _ := h _ hP; s = P.support} := by
  generalize_proofs
  ext x
  have : x ∈ (sSup S).support ↔ x ∈ SupSet.sSup (supportAddSubgroup '' S) := by
    simp [← supportAddSubgroup_sSup hSn hSd]
  rw [this,
      AddSubgroup.mem_sSup_of_directedOn (by simp_all)
        (.mono_comp (fun _ _ h ↦ supportAddSubgroup_mono h) hSd),
      Submodule.mem_sSup_of_directed]
  · aesop
  · rcases hSn with ⟨P, hP⟩
    exact ⟨let _ := h P hP; P.support, by aesop⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rcases hSd _ hx _ hy with ⟨z, hz, _, _⟩
    let _ := h _ hx
    let _ := h _ hy
    let _ := h _ hz
    exact ⟨z.support, by aesop (add safe apply support_mono)⟩

instance : (P'.comap f).HasIdealSupport where
  smul_mem_support x a ha := by simpa using smul_mem_support P' (f x) (by simpa using ha)

@[simp]
theorem comap_support : (P'.comap f).support = (P'.support).comap f := by
  ext x
  have := P'.comap_supportAddSubgroup f.toAddMonoidHom
  apply_fun (x ∈ ·) at this
  simpa

variable {f P} in
theorem HasIdealSupport.map (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set R) ⊆ P.supportAddSubgroup) : HasIdealSupport (P.map f) where
  smul_mem_support x a ha := by
    rw [map_supportAddSubgroup hsupp] at ha
    rcases ha with ⟨a', ha', rfl⟩
    rcases hf x with ⟨x', rfl⟩
    have := smul_mem_support P x' ha'
    aesop

-- TODO : comm
variable {f P} in
@[simp]
theorem map_support (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set R) ⊆ P.supportAddSubgroup) :
    letI _ := HasIdealSupport.map hf hsupp
    (P.map f).support = (P.support).map f := by
  ext x
  have := map_supportAddSubgroup hsupp
  apply_fun (x ∈ ·) at this
  simpa [Ideal.mem_map_iff_of_surjective f hf]

end AddSubmonoid

namespace Subsemiring

variable {R : Type*} [Ring R] (P : Subsemiring R)

namespace IsPreordering

variable [P.IsPreordering]

@[aesop unsafe 90% apply (rule_sets := [SetLike])]
theorem unitsInv_mem {a : Rˣ} (ha : ↑a ∈ P) : ↑a⁻¹ ∈ P := by
  have : (a * (a⁻¹ * a⁻¹) : R) ∈ P := by aesop (config := { enableSimp := false })
  simp_all

theorem one_notMem_supportAddSubgroup : 1 ∉ P.supportAddSubgroup :=
  fun h => P.neg_one_notMem h.2

theorem one_notMem_support [P.HasIdealSupport] : 1 ∉ P.support := by
  simpa using one_notMem_supportAddSubgroup P

theorem supportAddSubgroup_ne_top : P.supportAddSubgroup ≠ ⊤ :=
  fun h => P.neg_one_notMem (by simp [h] : 1 ∈ P.supportAddSubgroup).2

theorem support_ne_top [P.HasIdealSupport] : P.support ≠ ⊤ := by
  apply_fun Submodule.toAddSubgroup
  simpa using supportAddSubgroup_ne_top P

-- TODO : comm
theorem hasIdealSupport_of_isUnit_two (h : IsUnit (2 : R)) : P.HasIdealSupport := by
  rw [AddSubmonoid.hasIdealSupport_iff]
  intro x a _ _
  rcases h.exists_right_inv with ⟨half, h2⟩
  set y := (1 + x) * half
  set z := (1 - x) * half
  rw [show x = y ^ 2 - z ^ 2 by
    linear_combination (- x - x * half * 2) * h2]
  ring_nf
  aesop (add simp sub_eq_add_neg)

instance [h : Fact (IsUnit (2 : R))] : P.HasIdealSupport := hasIdealSupport_of_isUnit_two P h.out

section Field

variable {F : Type*} [Field F] (P : Subsemiring F) [P.IsPreordering]

@[aesop unsafe 90% apply (rule_sets := [SetLike])]
theorem inv_mem {a : F} (ha : a ∈ P) : a⁻¹ ∈ P := by
  have mem : a * (a⁻¹ * a⁻¹) ∈ P := by aesop
  field_simp at mem
  simp_all

instance : P.IsAddCone := AddSubmonoid.isAddCone_iff.mpr fun x _ _ ↦ by
  by_contra
  have mem : -x * x⁻¹ ∈ P := by aesop (erase simp neg_mul)
  field_simp at mem
  exact P.neg_one_notMem mem

instance : P.support.IsPrime := by simpa using Ideal.bot_prime

end Field

variable {P} in
theorem isOrdering_iff :
    P.IsOrdering ↔ ∀ a b : R, -(a * b) ∈ P → a ∈ P ∨ b ∈ P where
  mp _ a b _ := by
    by_contra
    have : ∀ (a : R), a ∈ P ∨ -a ∈ P := P.mem_or_neg_mem
    have : a * b ∈ P := by simpa using mul_mem (by grind : -a ∈ P) (by grind : -b ∈ P)
    have : a ∈ P.support ∨ b ∈ P.support :=
      Ideal.IsPrime.mem_or_mem inferInstance (by simp_all [AddSubmonoid.mem_support])
    simp_all [AddSubmonoid.mem_support]
  mpr h :=
    have : P.HasMemOrNegMem' := ⟨by simp [h]⟩
    { this with
      ne_top' := IsPreordering.support_ne_top P
      mem_or_mem' {x} {y} := by
        by_contra
        have := h (-x) y
        have := h (-x) (-y)
        have := h x y
        have := h x (-y)
        cases (by aesop : x ∈ P ∨ -x ∈ P) <;> simp_all [AddSubmonoid.mem_support]
    }

end IsPreordering

theorem IsPreordering.of_le {P Q : Subsemiring R} [P.IsPreordering] (hPQ : P ≤ Q) (hQ : -1 ∉ Q) :
    Q.IsPreordering where

theorem IsAddCone.eq_of_le {P Q : Subsemiring R} [P.HasMemOrNegMem'] (h : P ≤ Q) [Q.IsAddCone] :
    P = Q := eq_of_le_of_ge h <| by
  by_contra h2
  have ⟨x, hx, hx2⟩ : ∃ x, x ∈ Q ∧ x ∉ P := Set.not_subset.mp h2
  have : -x ∈ Q := by aesop (add unsafe forward (P.mem_or_neg_mem))
  have := AddSubmonoid.eq_zero_of_mem_of_neg_mem (S := Q.toAddSubmonoid) (x := x)
  simp_all

instance [IsSemireal R] : (sumSq R).IsPreordering where
  neg_one_notMem := by simpa using IsSemireal.not_isSumSq_neg_one

theorem _root_.isSemireal_ofIsPreordering [P.IsPreordering] : IsSemireal R :=
  .of_not_isSumSq_neg_one (P.neg_one_notMem <| P.mem_of_isSumSq ·)

theorem _root_.exists_isPreordering_iff_isSemireal :
    (∃ P : Subsemiring R, P.IsPreordering) ↔ IsSemireal R where
  mp | ⟨P, _⟩ => isSemireal_ofIsPreordering P
  mpr _ := ⟨sumSq R, inferInstance⟩

instance (P₁ P₂ : Subsemiring R) [P₁.IsPreordering] [P₂.IsPreordering] :
    (P₁ ⊓ P₂).IsPreordering where

theorem IsPreordering.sInf {S : Set (Subsemiring R)}
    (hSn : S.Nonempty) (hS : ∀ s ∈ S, s.IsPreordering) : (sInf S).IsPreordering where
  mem_of_isSquare x := by aesop (add simp Subsemiring.mem_sInf)
  neg_one_notMem := by
    have := hS _ hSn.some_mem
    simpa [Subsemiring.mem_sInf] using ⟨_, hSn.some_mem, hSn.some.neg_one_notMem⟩

theorem IsPreordering.sSup  {S : Set (Subsemiring R)}
    (hSn : S.Nonempty) (hSd : DirectedOn (· ≤ ·) S)
    (hS : ∀ s ∈ S, s.IsPreordering) : (sSup S).IsPreordering where
  mem_of_isSquare x := by
    have := Set.Nonempty.some_mem hSn
    simpa [mem_sSup_of_directedOn hSn hSd] using ⟨_, this, by aesop⟩
  neg_one_notMem := by
    simpa [mem_sSup_of_directedOn hSn hSd] using (fun x hx ↦ have := hS _ hx; neg_one_notMem x)

section comap

variable {A B : Type*} [Ring A] [Ring B] (f : A →+* B) (P : Subsemiring B)

-- TODO : replace non-primed version
@[simp]
theorem comap_toSubmonoid' : (P.comap f).toSubmonoid = P.toSubmonoid.comap f := by
  ext; simp

-- TODO : move to right place
@[simp]
theorem comap_toAddSubmonoid : (P.comap f).toAddSubmonoid = P.toAddSubmonoid.comap f := by
  ext; simp

/-- The preimage of an ordering along a ring homomorphism is an ordering. -/
instance [P.IsOrdering] : IsOrdering (comap f P) where
  __ : (P.comap f).HasMemOrNegMem' := by
    simpa using (inferInstance : (P.toAddSubmonoid.comap f).HasMemOrNegMem')
  __ : (P.comap f).support.IsPrime := by simp; infer_instance

/-- The preimage of a preordering along a ring homomorphism is a preordering. -/
instance [P.IsPreordering] : (P.comap f).IsPreordering where

end comap

section map

variable {A B : Type*} [Ring A] [Ring B] (f : A →+* B) (P : Subsemiring A)

-- TODO : replace non-primed version
@[simp]
theorem map_toSubmonoid' : (P.map f).toSubmonoid = P.toSubmonoid.map f := by
  ext; simp

-- TODO : move to right place
@[simp]
theorem map_toAddSubmonoid : (P.map f).toAddSubmonoid = P.toAddSubmonoid.map f := by
  ext; simp

variable {f P} in
/-- The image of an ordering `P` along a surjective ring homomorphism
with kernel contained in the support of `P` is an ordering. -/
theorem IsOrdering.map [P.IsOrdering] (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ P.supportAddSubgroup) : IsOrdering (P.map f) where
  __ : (P.map f).HasMemOrNegMem' := by
    simpa using AddSubmonoid.HasMemOrNegMem.map P.toAddSubmonoid hf
  __ : (P.map f).support.IsPrime := by
    simpa [AddSubmonoid.map_support hf hsupp] using Ideal.map_isPrime_of_surjective hf hsupp

variable {f P} in
theorem IsPreordering.map [P.IsPreordering] (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ P.supportAddSubgroup) : (P.map f).IsPreordering where
  mem_of_isSquare hx := by
    rcases isSquare_subset_image_isSquare hf hx with ⟨x, hx, hfx⟩
    exact ⟨x, by aesop⟩
  neg_one_notMem := fun ⟨x', hx', _⟩ => by
    have : -(x' + 1) + x' ∈ P := add_mem (hsupp (show f (x' + 1) = 0 by simp_all)).2 hx'
    aesop

end map

end Subsemiring
