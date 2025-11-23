/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import Mathlib.Algebra.Order.Ring.Ordering.Basic
import Mathlib.Algebra.Ring.Semireal.Defs
import Mathlib.RingTheory.Ideal.Maps

/-!

We prove basic properties of (pre)orderings on rings and their supports,
and define standard operations on them.

Note that the "preordering closure" of a set does not exist in general. The theory of
extending preorderings is given in `Algebra.Order.Ring.Ordering.Adjoin`.

## References

- [*An introduction to real algebra*, T.Y. Lam][lam_1984]

-/

variable {R : Type*} [CommRing R] {P : RingPreordering R}

/-!
### Preorderings
-/

namespace RingPreordering

/-!
### Supports
-/

theorem supportAddSubgroup_mono {Q : RingPreordering R} (h : P ≤ Q) :
    P.supportAddSubgroup ≤ Q.supportAddSubgroup :=
  fun _ ↦ by aesop (add simp mem_supportAddSubgroup)

theorem support_mono {Q : RingPreordering R} [P.HasIdealSupport] [Q.HasIdealSupport] (h : P ≤ Q) :
    P.support ≤ Q.support := fun _ ↦ by aesop (add simp mem_support)

/-! ## Order operations -/

section Inf
variable {P₁ P₂ : RingPreordering R}

instance : Min (RingPreordering R) where
  min P₁ P₂ := { toSubsemiring := min P₁.toSubsemiring P₂.toSubsemiring }

@[simp]
theorem inf_toSubsemiring : (P₁ ⊓ P₂).toSubsemiring = P₁.toSubsemiring ⊓ P₂.toSubsemiring := rfl
@[simp] theorem mem_inf {x : R} : x ∈ P₁ ⊓ P₂ ↔ x ∈ P₁ ∧ x ∈ P₂ := .rfl
@[simp, norm_cast] theorem coe_inf : ↑(P₁ ⊓ P₂) = (P₁ ∩ P₂ : Set R) := rfl

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

instance : SemilatticeInf (RingPreordering R) where
  inf := (· ⊓ ·)
  inf_le_left _ _ := by simp_all [← SetLike.coe_subset_coe]
  inf_le_right _ _ := by simp_all [← SetLike.coe_subset_coe]
  le_inf _ _ _ _ _ := by simp_all [← SetLike.coe_subset_coe]

end Inf

section sInf
variable {S : Set (RingPreordering R)} {hS : S.Nonempty}

variable (hS) in
def sInf {S : Set (RingPreordering R)} (hS : S.Nonempty) : RingPreordering R where
  __ := InfSet.sInf (RingPreordering.toSubsemiring '' S)
  mem_of_isSquare' x := by aesop (add simp Submonoid.mem_iInf)
  neg_one_notMem' := by simpa [Submonoid.mem_iInf] using
    ⟨_, Set.Nonempty.some_mem hS, RingPreordering.neg_one_notMem _⟩

@[simp]
theorem sInf_toSubsemiring :
  (sInf hS).toSubsemiring = InfSet.sInf (RingPreordering.toSubsemiring '' S) := rfl

@[simp, norm_cast]
theorem coe_sInf : (sInf hS : Set R) = ⋂ P ∈ S, P := by
  have : (sInf hS : Set R) = ⋂ P ∈ (RingPreordering.toSubsemiring '' S), P := rfl
  simp_all

@[simp]
theorem mem_sInf {x : R} : x ∈ sInf hS ↔ ∀ p ∈ S, x ∈ p := by
  rw [show x ∈ sInf hS ↔ x ∈ (sInf hS : Set R) by simp [-coe_sInf]]
  simp_all

@[simp]
theorem supportAddSubgroup_sInf :
    (sInf hS).supportAddSubgroup = InfSet.sInf (supportAddSubgroup '' S) := by
  aesop (add simp mem_supportAddSubgroup)

theorem hasIdealSupport_sInf (h : ∀ P ∈ S, P.HasIdealSupport) : (sInf hS).HasIdealSupport := by
  simp_all [hasIdealSupport_iff]

@[simp]
theorem support_sInf (h : ∀ P ∈ S, P.HasIdealSupport) :
    letI _ := hasIdealSupport_sInf h
    (sInf hS).support = InfSet.sInf {s | ∃ P, ∃ hP : P ∈ S, letI _ := h _ hP; s = P.support} := by
  aesop (add simp mem_support)

variable (hS) in
theorem sInf_le {P} (hP : P ∈ S) : sInf hS ≤ P := by
  rw [← SetLike.coe_subset_coe]
  simpa using Set.biInter_subset_of_mem hP

variable (hS) in
theorem le_sInf {P} (hP : ∀ Q ∈ S, P ≤ Q) : P ≤ sInf hS := by
  rw [← SetLike.coe_subset_coe]
  simpa using Set.subset_iInter₂ hP

end sInf

section Bot
variable [IsSemireal R]

instance : Bot (RingPreordering R) where
  bot := { toSubsemiring := Subsemiring.sumSq R
           neg_one_notMem' := by simpa using IsSemireal.not_isSumSq_neg_one }

@[simp] theorem bot_toSubsemiring : (⊥ : RingPreordering R).toSubsemiring = .sumSq R := rfl

@[simp] theorem mem_bot {a} : a ∈ (⊥ : RingPreordering R) ↔ IsSumSq a :=
  show a ∈ Subsemiring.sumSq R ↔ IsSumSq a by simp

@[simp, norm_cast] theorem coe_bot : (⊥ : RingPreordering R) = {x : R | IsSumSq x} :=
  show Subsemiring.sumSq R = {x : R | IsSumSq x} by simp

instance : OrderBot (RingPreordering R) where
  bot := ⊥
  bot_le P a := by aesop

end Bot

section sSup
variable {S : Set (RingPreordering R)} {hS : S.Nonempty} {hSd : DirectedOn (· ≤ ·) S}

variable (hS) (hSd) in
def sSup : RingPreordering R where
  __ := SupSet.sSup (toSubsemiring '' S)
  mem_of_isSquare' x := by
    have : DirectedOn (· ≤ ·) (toSubsemiring '' S) := directedOn_image.mpr hSd
    aesop (add simp Subsemiring.mem_sSup_of_directedOn,
               unsafe forward (Set.Nonempty.some_mem hS))
  neg_one_notMem' := by
    have : DirectedOn (· ≤ ·) (toSubsemiring '' S) := directedOn_image.mpr hSd
    aesop (add simp Subsemiring.mem_sSup_of_directedOn,
               unsafe forward (Set.Nonempty.some_mem hS))

@[simp]
theorem sSup_toSubsemiring :
  (sSup hS hSd).toSubsemiring = SupSet.sSup (RingPreordering.toSubsemiring '' S) := rfl

@[simp, norm_cast]
theorem coe_sSup : (sSup hS hSd : Set R) = ⋃ P ∈ S, P := by
  have : (sSup hS hSd : Set R) = SupSet.sSup (toSubsemiring '' S) := rfl
  simp_all [Subsemiring.coe_sSup_of_directedOn (by aesop) <| directedOn_image.mpr hSd]

@[simp]
theorem mem_sSup {x : R} : x ∈ sSup hS hSd ↔ ∃ p ∈ S, x ∈ p := by
  rw [show x ∈ sSup hS hSd ↔ x ∈ (sSup hS hSd : Set R) by simp [-coe_sSup]]
  simp_all

include hSd in
variable (hSd) in
theorem directedOn_image_supportAddSubgroup :
    DirectedOn (fun x1 x2 ↦ x1 ≤ x2) (supportAddSubgroup '' S) := by
  rw [directedOn_image]
  intro _ hx _ hy
  rcases hSd _ hx _ hy with ⟨z, _⟩
  exact ⟨z, by aesop (add safe apply supportAddSubgroup_mono)⟩

@[simp]
theorem supportAddSubgroup_sSup :
    (sSup hS hSd).supportAddSubgroup = SupSet.sSup (supportAddSubgroup '' S) := by
  ext x
  rw [AddSubgroup.mem_sSup_of_directedOn (by simp_all) (directedOn_image_supportAddSubgroup hSd)]
  simp only [mem_supportAddSubgroup, mem_sSup, Set.mem_image, exists_exists_and_eq_and]
  refine ⟨?_, by aesop⟩
  rintro ⟨⟨_, hs₁, _⟩, ⟨_, hs₂, _⟩⟩
  rcases hSd _ hs₁ _ hs₂ with ⟨s, hs⟩
  exact ⟨s, by aesop⟩

theorem hasIdealSupport_sSup (h : ∀ P ∈ S, P.HasIdealSupport) : (sSup hS hSd).HasIdealSupport := by
  simp_rw [hasIdealSupport_iff, mem_sSup] at *
  rintro x a ⟨P, hP, hP'⟩ ⟨Q, hQ, hQ'⟩
  rcases hSd _ hP _ hQ with ⟨R, hR, hPR, hQR⟩
  have := h _ hR x a (hPR hP') (hQR hQ')
  aesop

@[simp]
theorem support_sSup  (h : ∀ P ∈ S, P.HasIdealSupport) :
    letI _ : (sSup hS hSd).HasIdealSupport := hasIdealSupport_sSup h
    (sSup hS hSd).support = SupSet.sSup {s | ∃ P, ∃ hP : P ∈ S, letI _ := h _ hP; s = P.support} := by
  generalize_proofs
  ext x
  have := supportAddSubgroup_sSup (hS := hS) (hSd := hSd)
  apply_fun (x ∈ ·) at this
  simp only [supportAddSubgroup_eq, Submodule.mem_toAddSubgroup] at this
  rw [this,
      AddSubgroup.mem_sSup_of_directedOn (by simp_all) (directedOn_image_supportAddSubgroup hSd)]
  rw [Submodule.mem_sSup_of_directed]
  · aesop
  · rcases hS with ⟨P, hP⟩
    exact ⟨let _ := h P hP; P.support, by aesop⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rcases hSd _ hx _ hy with ⟨z, hz, _, _⟩
    let _ := h _ hx
    let _ := h _ hy
    let _ := h _ hz
    exact ⟨z.support, by aesop (add safe apply support_mono)⟩

variable (hS) (hSd) in
theorem le_sSup {P} (hP : P ∈ S) : P ≤ sSup hS hSd := by
  rw [← SetLike.coe_subset_coe]
  simpa using Set.subset_biUnion_of_mem hP

variable (hS) (hSd) in
theorem sSup_le {P} (hP : ∀ Q ∈ S, Q ≤ P) : sSup hS hSd ≤ P := by
  rw [← SetLike.coe_subset_coe]
  simpa using Set.iUnion₂_subset hP

end sSup

theorem nonempty_chain_bddAbove {S : Set (RingPreordering R)}
    (hS : S.Nonempty) (hSc : IsChain (· ≤ ·) S) : BddAbove S :=
  ⟨sSup hS <| IsChain.directedOn hSc, fun _ => le_sSup hS <| IsChain.directedOn hSc⟩

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-! ## comap -/

/-- The preimage of a preordering along a ring homomorphism is a preordering. -/
def comap (f : A →+* B) (P : RingPreordering B) : RingPreordering A where
  __ := P.toSubsemiring.comap f
  mem_of_isSquare' := by aesop

@[simp]
theorem coe_comap (P : RingPreordering B) {f : A →+* B} : (P.comap f : Set A) = f ⁻¹' P := rfl

@[simp]
theorem mem_comap {P : RingPreordering B} {f : A →+* B} {x : A} : x ∈ P.comap f ↔ f x ∈ P :=
  .rfl

theorem comap_comap (P : RingPreordering C) (g : B →+* C) (f : A →+* B) :
    (P.comap g).comap f = P.comap (g.comp f) := rfl

instance (P : RingPreordering B) [HasMemOrNegMem P] (f : A →+* B) : HasMemOrNegMem (comap f P) where
  mem_or_neg_mem x := by have := mem_or_neg_mem P (f x); aesop

@[simp]
theorem mem_comap_supportAddSubgroup {P : RingPreordering B} {f : A →+* B} {x : A} :
    x ∈ supportAddSubgroup (P.comap f) ↔ f x ∈ P.supportAddSubgroup := by
  simp [mem_supportAddSubgroup]

@[simp]
theorem comap_supportAddSubgroup {P : RingPreordering B} {f : A →+* B} :
    supportAddSubgroup (P.comap f) = (P.supportAddSubgroup).comap f := by ext; simp

instance (P : RingPreordering B) [P.HasIdealSupport] (f : A →+* B) :
    HasIdealSupport (P.comap f) where
  smul_mem_support x a ha := by have := smul_mem_support P (f x) (by simpa using ha); simp_all

@[simp]
theorem mem_comap_support {P : RingPreordering B} [P.HasIdealSupport] {f : A →+* B} {x : A} :
    x ∈ (P.comap f).support ↔ f x ∈ P.support := by
  simpa using mem_comap_supportAddSubgroup (P := P)

@[simp]
theorem comap_support {P : RingPreordering B} [P.HasIdealSupport] {f : A →+* B} :
    (P.comap f).support = (P.support).comap f := by ext; simp

/-- The preimage of an ordering along a ring homomorphism is an ordering. -/
instance (P : RingPreordering B) [P.IsOrdering] (f : A →+* B) : IsOrdering (comap f P) where
  __ : (P.comap f).support.IsPrime := by rw [comap_support]; infer_instance

/-! ## map -/

/-- The image of a preordering `P` along a surjective ring homomorphism
  with kernel contained in the support of `P` is a preordering. -/
def map {f : A →+* B} {P : RingPreordering A} (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ P.supportAddSubgroup) : RingPreordering B where
  __ := P.toSubsemiring.map f
  mem_of_isSquare' hx := by
    rcases isSquare_subset_image_isSquare hf hx with ⟨x, hx, hfx⟩
    use x
    aesop
  neg_one_notMem' := fun ⟨x', hx', _⟩ => by
    have : -(x' + 1) + x' ∈ P := add_mem (hsupp (show f (x' + 1) = 0 by simp_all)).2 hx'
    aesop

@[simp]
theorem coe_map {f : A →+* B} {P : RingPreordering A} (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ P.supportAddSubgroup) :
    (map hf hsupp : Set B) = f '' P := rfl

@[simp]
theorem mem_map {f : A →+* B} {P : RingPreordering A} (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ P.supportAddSubgroup) {y} :
    y ∈ map hf hsupp ↔ ∃ x ∈ P, f x = y := .rfl

instance {f : A →+* B} {P : RingPreordering A} [HasMemOrNegMem P] (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ P.supportAddSubgroup) : HasMemOrNegMem (map hf hsupp) where
  mem_or_neg_mem x := by
    obtain ⟨x', rfl⟩ := hf x
    have := mem_or_neg_mem P x'
    aesop

@[simp]
theorem mem_map_supportAddSubgroup {f : A →+* B} {P : RingPreordering A}
    {hf : Function.Surjective f} {hsupp : (RingHom.ker f : Set A) ⊆ P.supportAddSubgroup} {x : B} :
    x ∈ supportAddSubgroup (map hf hsupp) ↔ ∃ y ∈ P.supportAddSubgroup, f y = x := by
  refine ⟨fun ⟨⟨a, ⟨ha₁, ha₂⟩⟩, ⟨b, ⟨hb₁, hb₂⟩⟩⟩ => ?_, by aesop (add simp mem_supportAddSubgroup)⟩
  have : -(a + b) + b ∈ P := by exact add_mem (hsupp (show f (a + b) = 0 by simp_all)).2 hb₁
  aesop (add simp mem_supportAddSubgroup)

@[simp]
theorem map_supportAddSubgroup {f : A →+* B} {P : RingPreordering A} {hf : Function.Surjective f}
    {hsupp : (RingHom.ker f : Set A) ⊆ P.supportAddSubgroup} :
    supportAddSubgroup (map hf hsupp) = (P.supportAddSubgroup).map f := by ext; simp

instance {f : A →+* B} {P : RingPreordering A} [P.HasIdealSupport] (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ P.supportAddSubgroup) :
    HasIdealSupport <| map hf hsupp where
  smul_mem_support x a ha := by
    rw [mem_map_supportAddSubgroup] at ha
    rcases ha with ⟨a', ha', rfl⟩
    rcases hf x with ⟨x', rfl⟩
    have := smul_mem_support P x' ha'
    aesop

@[simp]
theorem mem_map_support {f : A →+* B} {P : RingPreordering A} [P.HasIdealSupport]
    {hf : Function.Surjective f}
    {hsupp : RingHom.ker f ≤ P.support} {x : B} :
    x ∈ (map hf hsupp).support ↔ ∃ y ∈ P.support, f y = x := by
  simpa using mem_map_supportAddSubgroup

@[simp]
theorem map_support {f : A →+* B} {P : RingPreordering A} [P.HasIdealSupport]
    {hf : Function.Surjective f} {hsupp : RingHom.ker f ≤ P.support} :
    (map hf hsupp).support = (P.support).map f := by
  ext; simp [Ideal.mem_map_iff_of_surjective f hf]

/-- The image of an ordering `P` along a surjective ring homomorphism
  with kernel contained in the support of `P` is an ordering. -/
instance {f : A →+* B} {P : RingPreordering A} [P.IsOrdering] (hf : Function.Surjective f)
    (hsupp : RingHom.ker f ≤ P.support) : IsOrdering <| map hf hsupp where
  __ : (map hf hsupp).support.IsPrime := by
    simpa using Ideal.map_isPrime_of_surjective hf hsupp

end RingPreordering
