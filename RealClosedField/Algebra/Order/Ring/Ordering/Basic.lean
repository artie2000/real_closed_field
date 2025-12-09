
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

variable {R : Type*} [CommRing R] (P : Subsemiring R)

-- TODO : separate out the parts that don't need `IsPreordering` or `Subsemiring`

/-!
### Preorderings
-/

namespace Subsemiring

/-!
### Supports
-/

theorem supportAddSubgroup_mono {P Q : Subsemiring R} (h : P ≤ Q) :
    P.supportAddSubgroup ≤ Q.supportAddSubgroup :=
  fun _ ↦ by aesop (add simp mem_supportAddSubgroup)

theorem support_mono {P Q : Subsemiring R} [P.HasIdealSupport] [Q.HasIdealSupport] (h : P ≤ Q) :
    P.support ≤ Q.support := fun _ ↦ by aesop (add simp mem_support)

theorem HasIdealSupport.smul_mem [P.HasIdealSupport]
    (x : R) {a : R} (h₁a : a ∈ P) (h₂a : -a ∈ P) : x * a ∈ P := by
  grind [hasIdealSupport_iff]

theorem HasIdealSupport.neg_smul_mem [P.HasIdealSupport]
    (x : R) {a : R} (h₁a : a ∈ P) (h₂a : -a ∈ P) : -(x * a) ∈ P := by
  grind [hasIdealSupport_iff]

-- TODO : figure out namespacing (for dot notation)

namespace IsPreordering

variable [P.IsPreordering]

@[aesop unsafe 90% apply (rule_sets := [SetLike])]
theorem unitsInv_mem {a : Rˣ} (ha : ↑a ∈ P) : ↑a⁻¹ ∈ P := by
  have : (a * (a⁻¹ * a⁻¹) : R) ∈ P := by aesop (config := { enableSimp := false })
  simp_all

@[aesop unsafe 90% apply (rule_sets := [SetLike])]
theorem inv_mem {F : Type*} [Field F] (P : Subsemiring F) [P.IsPreordering] {a : F} (ha : a ∈ P) :
    a⁻¹ ∈ P := by
  have mem : a * (a⁻¹ * a⁻¹) ∈ P := by aesop
  field_simp at mem
  simp_all

section mk'

variable {R : Type*} [CommRing R] {P : Set R} {add} {mul} {sq} {neg_one}

/-- Construct a preordering from a minimal set of axioms. -/
def mk' {R : Type*} [CommRing R] (P : Set R)
    (add : ∀ {x y : R}, x ∈ P → y ∈ P → x + y ∈ P)
    (mul : ∀ {x y : R}, x ∈ P → y ∈ P → x * y ∈ P)
    (sq : ∀ x : R, x * x ∈ P)
    (neg_one : -1 ∉ P) :
    Subsemiring R where
  carrier := P
  add_mem' {x y} := by simpa using add
  mul_mem' {x y} := by simpa using mul
  zero_mem' := by simpa using sq 0
  one_mem' := by simpa using sq 1

@[simp] theorem mem_mk' {x : R} : x ∈ mk' P add mul sq neg_one ↔ x ∈ P := .rfl
@[simp, norm_cast] theorem coe_mk' : mk' P add mul sq neg_one = P := rfl

instance : IsPreordering (mk' P add mul sq neg_one) where

end mk'

/-!
### Supports
-/

section ne_top

theorem one_notMem_supportAddSubgroup : 1 ∉ P.supportAddSubgroup :=
  fun h => P.neg_one_notMem h.2

theorem one_notMem_support [P.HasIdealSupport] : 1 ∉ P.support := by
  simpa using one_notMem_supportAddSubgroup P

theorem supportAddSubgroup_ne_top : P.supportAddSubgroup ≠ ⊤ :=
  fun h => P.neg_one_notMem (by simp [h] : 1 ∈ P.supportAddSubgroup).2

theorem support_ne_top [P.HasIdealSupport] : P.support ≠ ⊤ := by
  apply_fun Submodule.toAddSubgroup
  simpa using supportAddSubgroup_ne_top P

end ne_top

theorem hasIdealSupport_of_isUnit_two (h : IsUnit (2 : R)) : P.HasIdealSupport := by
  rw [hasIdealSupport_iff]
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

variable {P} in
protected theorem eq_zero_of_mem_of_neg_mem {x} (h : x ∈ P) (h2 : -x ∈ P) : x = 0 := by
  by_contra
  have mem : -x * x⁻¹ ∈ P := by aesop (erase simp neg_mul)
  field_simp at mem
  exact P.neg_one_notMem mem

theorem supportAddSubgroup_eq_bot : P.supportAddSubgroup = ⊥ := by
  ext
  grind [mem_supportAddSubgroup, AddSubgroup.mem_bot, IsPreordering.eq_zero_of_mem_of_neg_mem,
         AddSubgroup.zero_mem]

instance : P.HasIdealSupport where
  smul_mem_support := by simp [supportAddSubgroup_eq_bot]

@[simp] theorem support_eq_bot : P.support = ⊥ := by
  simpa [← Submodule.toAddSubgroup_inj] using supportAddSubgroup_eq_bot P

instance : P.support.IsPrime := by simpa using Ideal.bot_prime

end Field

end IsPreordering

/-- Constructor for IsOrdering that doesn't require `ne_top'`. -/
theorem IsOrdering.mk' [P.IsPreordering] [HasMemOrNegMem P]
    (h : ∀ {x y}, x * y ∈ P.support → x ∈ P.support ∨ y ∈ P.support) : P.IsOrdering where
  ne_top' := IsPreordering.support_ne_top P
  mem_or_mem' := h

variable {P} in
theorem isOrdering_iff [P.IsPreordering] :
    P.IsOrdering ↔ ∀ a b : R, -(a * b) ∈ P → a ∈ P ∨ b ∈ P := by
  refine ⟨fun _ a b _ => ?_, fun h => ?_⟩
  · by_contra
    have : a * b ∈ P := by simpa using mul_mem (by aesop : -a ∈ P) (by aesop : -b ∈ P)
    have : a ∈ P.support ∨ b ∈ P.support :=
      Ideal.IsPrime.mem_or_mem inferInstance (by simp_all [mem_support])
    simp_all [mem_support]
  · have : HasMemOrNegMem P := ⟨by simp [h]⟩
    refine IsOrdering.mk' P (fun {x y} _ => ?_)
    by_contra
    have := h (-x) y
    have := h (-x) (-y)
    have := h x y
    have := h x (-y)
    cases (by aesop : x ∈ P ∨ -x ∈ P) <;> simp_all [mem_support]

/-! ## Order operations -/

theorem IsPreordering.of_le [P.IsPreordering] {Q : Subsemiring R} (hPQ : P ≤ Q) (hQ : -1 ∉ Q) :
    Q.IsPreordering where

instance [IsSemireal R] : (sumSq R).IsPreordering where
  neg_one_notMem := by simpa using IsSemireal.not_isSumSq_neg_one

theorem isSemireal_ofIsPreordering [P.IsPreordering] : IsSemireal R :=
  .of_not_isSumSq_neg_one (P.neg_one_notMem <| P.mem_of_isSumSq ·)

theorem _root_.exists_isPreordering_iff_isSemireal :
    (∃ P : Subsemiring R, P.IsPreordering) ↔ IsSemireal R where
  mp | ⟨P, _⟩ => isSemireal_ofIsPreordering P
  mpr _ := ⟨sumSq R, inferInstance⟩

section Inf

variable (P₁ P₂ : Subsemiring R)

instance [P₁.IsPreordering] [P₂.IsPreordering] : (P₁ ⊓ P₂).IsPreordering where

@[simp]
theorem supportAddSubgroup_inf :
    (P₁ ⊓ P₂).supportAddSubgroup = P₁.supportAddSubgroup ⊓ P₂.supportAddSubgroup := by
  aesop (add simp mem_supportAddSubgroup)

instance [P₁.HasIdealSupport] [P₂.HasIdealSupport] : (P₁ ⊓ P₂).HasIdealSupport := by
  simp_all [hasIdealSupport_iff]

@[simp]
theorem support_inf [P₁.HasIdealSupport] [P₂.HasIdealSupport] :
    (P₁ ⊓ P₂).support = P₁.support ⊓ P₂.support := by
  apply_fun Submodule.toAddSubgroup using Submodule.toAddSubgroup_injective
  simpa [-Submodule.toAddSubgroup_inj] using supportAddSubgroup_inf (P₁ := P₁) (P₂ := P₂)

end Inf

section sInf

variable (S : Set (Subsemiring R))

variable {S} in
theorem IsPreordering.sInf (hSn : S.Nonempty) (hS : ∀ s ∈ S, s.IsPreordering) :
    (sInf S).IsPreordering where
  mem_of_isSquare x := by aesop (add simp Subsemiring.mem_sInf)
  neg_one_notMem := by
    have := hS _ hSn.some_mem
    simpa [Subsemiring.mem_sInf] using ⟨_, hSn.some_mem, hSn.some.neg_one_notMem⟩

@[simp]
theorem supportAddSubgroup_sInf :
    (sInf S).supportAddSubgroup = InfSet.sInf (supportAddSubgroup '' S) := by
  ext
  aesop (add simp mem_supportAddSubgroup, simp mem_sInf)

variable {S} in
theorem HasIdealSupport.sInf (h : ∀ P ∈ S, P.HasIdealSupport) : (sInf S).HasIdealSupport := by
  simp_all [hasIdealSupport_iff, mem_sInf]

variable {S} in
@[simp]
theorem support_sInf (h : ∀ P ∈ S, P.HasIdealSupport) :
    letI _ := HasIdealSupport.sInf h
    (sInf S).support = InfSet.sInf {s | ∃ P, ∃ hP : P ∈ S, letI _ := h _ hP; s = P.support} := by
  aesop (add simp mem_support, simp mem_sInf)

end sInf

section sSup
variable (S : Set (Subsemiring R))

variable {S} in
instance isPreordering_sSup (hSn : S.Nonempty) (hSd : DirectedOn (· ≤ ·) S)
    (hS : ∀ s ∈ S, s.IsPreordering) : (sSup S).IsPreordering where
  mem_of_isSquare x := by
    have := Set.Nonempty.some_mem hSn
    simpa [mem_sSup_of_directedOn hSn hSd] using ⟨_, this, by aesop⟩
  neg_one_notMem := by
    simpa [mem_sSup_of_directedOn hSn hSd] using (fun x hx ↦ have := hS _ hx; neg_one_notMem x)

variable {S} in
@[simp]
theorem supportAddSubgroup_sSup (hSn : S.Nonempty) (hSd : DirectedOn (· ≤ ·) S) :
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

variable {S} in
protected theorem HasIdealSupport.sSup (hSn : S.Nonempty) (hSd : DirectedOn (· ≤ ·) S)
    (h : ∀ P ∈ S, P.HasIdealSupport) : (sSup S).HasIdealSupport := by
  simp only [hasIdealSupport_iff, mem_sSup_of_directedOn, forall_exists_index, and_imp, *] at *
  rintro x a P hP hP' Q hQ hQ'
  rcases hSd _ hP _ hQ with ⟨R, hR, hPR, hQR⟩
  have := h _ hR x a (hPR hP') (hQR hQ')
  exact ⟨⟨R, hR, this.1⟩, ⟨R, hR, this.2⟩⟩

variable {S} in
@[simp]
theorem support_sSup (hSn : S.Nonempty) (hSd : DirectedOn (· ≤ ·) S)
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

end sSup

variable {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)

/-! ## comap -/

section comap

variable (P : Subsemiring B)

/-- The preimage of a preordering along a ring homomorphism is a preordering. -/
instance [P.IsPreordering] : (P.comap f).IsPreordering where

instance [P.IsPreordering] [HasMemOrNegMem P] : HasMemOrNegMem (P.comap f) where
  mem_or_neg_mem x := by have := mem_or_neg_mem P (f x); aesop

@[simp]
theorem comap_supportAddSubgroup :
    (P.comap f).supportAddSubgroup = (P.supportAddSubgroup).comap f := by
  ext; simp [mem_supportAddSubgroup]

instance [P.HasIdealSupport] : HasIdealSupport (P.comap f) where
  smul_mem_support x a ha := by have := smul_mem_support P (f x) (by simpa using ha); simp_all

@[simp]
theorem comap_support [P.HasIdealSupport] : (P.comap f).support = (P.support).comap f := by
  ext x
  have := comap_supportAddSubgroup f P
  apply_fun (x ∈ ·) at this
  simpa

/-- The preimage of an ordering along a ring homomorphism is an ordering. -/
instance [P.IsOrdering] : IsOrdering (comap f P) where
  __ : (P.comap f).support.IsPrime := by rw [comap_support]; infer_instance

end comap

/-! ## map -/

section map

variable (P : Subsemiring A)

variable {f P} in
theorem IsPreordering.map [P.IsPreordering] (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ P.supportAddSubgroup) : (P.map f).IsPreordering where
  mem_of_isSquare hx := by
    rcases isSquare_subset_image_isSquare hf hx with ⟨x, hx, hfx⟩
    exact ⟨x, by aesop⟩
  neg_one_notMem := fun ⟨x', hx', _⟩ => by
    have : -(x' + 1) + x' ∈ P := add_mem (hsupp (show f (x' + 1) = 0 by simp_all)).2 hx'
    aesop

variable {f} in
theorem HasMemOrNegMem.map [HasMemOrNegMem P] (hf : Function.Surjective f) :
    HasMemOrNegMem (P.map f) where
  mem_or_neg_mem x := by
    obtain ⟨x', rfl⟩ := hf x
    have := mem_or_neg_mem P x'
    aesop

variable {f P} in
@[simp]
theorem map_supportAddSubgroup
    (hsupp : (RingHom.ker f : Set A) ⊆ P.supportAddSubgroup) :
    (P.map f).supportAddSubgroup = (P.supportAddSubgroup).map f := by
  ext
  refine ⟨fun ⟨⟨a, ⟨ha₁, ha₂⟩⟩, ⟨b, ⟨hb₁, hb₂⟩⟩⟩ => ?_, by aesop (add simp mem_supportAddSubgroup)⟩
  have : -(a + b) + b ∈ P := by exact add_mem (hsupp (show f (a + b) = 0 by simp_all)).2 hb₁
  aesop (add simp mem_supportAddSubgroup)

variable {f P} in
theorem HasIdealSupport.map [P.HasIdealSupport] (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ P.supportAddSubgroup) : HasIdealSupport (P.map f) where
  smul_mem_support x a ha := by
    rw [map_supportAddSubgroup hsupp] at ha
    rcases ha with ⟨a', ha', rfl⟩
    rcases hf x with ⟨x', rfl⟩
    have := smul_mem_support P x' ha'
    aesop

variable {f P} in
@[simp]
theorem map_support [P.HasIdealSupport] (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ P.supportAddSubgroup) :
    letI _ := HasIdealSupport.map hf hsupp
    (P.map f).support = (P.support).map f := by
  ext x
  have := map_supportAddSubgroup hsupp
  apply_fun (x ∈ ·) at this
  simpa [Ideal.mem_map_iff_of_surjective f hf]

variable {f P} in
/-- The image of an ordering `P` along a surjective ring homomorphism
with kernel contained in the support of `P` is an ordering. -/
theorem IsOrdering.map [P.IsOrdering] (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ P.supportAddSubgroup) : IsOrdering (P.map f) where
  __ := IsPreordering.map hf hsupp
  __ := HasMemOrNegMem.map P hf
  __ : (P.map f).support.IsPrime := by
    simpa [map_support hf hsupp] using Ideal.map_isPrime_of_surjective hf hsupp

end map

end Subsemiring
