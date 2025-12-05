/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import Mathlib.Algebra.Order.Ring.Ordering.Basic
import Mathlib.Algebra.Ring.Semireal.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.Maps

/-!

We prove basic properties of (pre)orderings on rings and their supports,
and define standard operations on them.

Note that the "preordering closure" of a set does not exist in general. The theory of
extending preorderings is given in `Algebra.Order.Ring.Ordering.Adjoin`.

## References

- [*An introduction to real algebra*, T.Y. Lam][lam_1984]

-/

theorem isSemireal_iff_not_isSumSq_neg_one {R : Type*} [AddGroup R] [One R] [Mul R] :
    IsSemireal R ↔ ¬ IsSumSq (-1 : R) where
  mp _ := IsSemireal.not_isSumSq_neg_one
  mpr h := ⟨by aesop (add simp add_eq_zero_iff_neg_eq)⟩

alias ⟨_, IsSemireal.of_not_isSumSq_neg_one⟩ := isSemireal_iff_not_isSumSq_neg_one

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

section Bot

variable [IsSemireal R]

instance : Bot (RingPreordering R) where
  bot.toSubsemiring := Subsemiring.sumSq R
  bot.neg_one_notMem' := by simpa using IsSemireal.not_isSumSq_neg_one

@[simp] theorem bot_toSubsemiring : (⊥ : RingPreordering R).toSubsemiring = .sumSq R := rfl

@[simp] theorem mem_bot (a) : a ∈ (⊥ : RingPreordering R) ↔ IsSumSq a :=
  show a ∈ Subsemiring.sumSq R ↔ IsSumSq a by simp

@[simp, norm_cast] theorem coe_bot : (⊥ : RingPreordering R) = {x : R | IsSumSq x} :=
  show Subsemiring.sumSq R = {x : R | IsSumSq x} by simp

instance : OrderBot (RingPreordering R) where
  bot_le P a := by aesop

end Bot

theorem isSemireal (P : RingPreordering R) : IsSemireal R :=
  .of_not_isSumSq_neg_one (P.neg_one_notMem <| RingPreordering.mem_of_isSumSq ·)

theorem _root_.nonempty_ringPreordering_iff_isSemireal :
    Nonempty (RingPreordering R) ↔ IsSemireal R where
  mp | ⟨P⟩ => P.isSemireal
  mpr _ := ⟨⊥⟩

section Inf

variable (P₁ P₂ : RingPreordering R)

instance : Min (RingPreordering R) where
  min P₁ P₂ := { toSubsemiring := min P₁.toSubsemiring P₂.toSubsemiring }

@[simp]
theorem toSubsemiring_inf : (P₁ ⊓ P₂).toSubsemiring = P₁.toSubsemiring ⊓ P₂.toSubsemiring := rfl
@[simp] theorem mem_inf (x : R) : x ∈ P₁ ⊓ P₂ ↔ x ∈ P₁ ∧ x ∈ P₂ := .rfl
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

variable [IsSemireal R] {S : Set (RingPreordering R)}

variable (S) in
/-- The intersection of a nonempty set of preorderings is a ring preordering. -/
noncomputable def sInf : RingPreordering R where
  __ := open Classical in
    if S.Nonempty then
      InfSet.sInf (RingPreordering.toSubsemiring '' S) else
      (⊥ : RingPreordering R).toSubsemiring
  mem_of_isSquare' x := by split_ifs <;> aesop (add simp Submonoid.mem_iInf)
  neg_one_notMem' := by
    split_ifs with hS
    · simpa [Submonoid.mem_iInf] using
        ⟨_, Set.Nonempty.some_mem hS, RingPreordering.neg_one_notMem _⟩
    · simpa using IsSemireal.not_isSumSq_neg_one

@[simp]
theorem sInf_toSubsemiring (hS : S.Nonempty) :
  (sInf S).toSubsemiring = InfSet.sInf (RingPreordering.toSubsemiring '' S) := by simp [sInf, hS]

@[simp, norm_cast]
theorem coe_sInf (hS : S.Nonempty) : (sInf S : Set R) = ⋂ P ∈ S, P := by
  have : (sInf S : Set R) = ⋂ P ∈ (RingPreordering.toSubsemiring '' S), P := by simp [sInf, hS]
  simp_all

@[simp]
theorem mem_sInf {hS : S.Nonempty} {x : R} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := by
  simp [← SetLike.mem_coe, hS]

@[simp]
theorem supportAddSubgroup_sInf (hS : S.Nonempty) :
    (sInf S).supportAddSubgroup = InfSet.sInf (supportAddSubgroup '' S) := by
  aesop (add simp mem_supportAddSubgroup)

protected theorem HasIdealSupport.sInf (hS : S.Nonempty) (h : ∀ P ∈ S, P.HasIdealSupport) :
    (sInf S).HasIdealSupport := by
  simp_all [hasIdealSupport_iff]

@[simp]
theorem support_sInf (hS : S.Nonempty) (h : ∀ P ∈ S, P.HasIdealSupport) :
    letI _ := HasIdealSupport.sInf hS h
    (sInf S).support =
    InfSet.sInf {s | ∃ P, ∃ hP : P ∈ S, letI _ := h _ hP; s = P.support} := by
  aesop (add simp mem_support)

theorem sInf_le (hS : S.Nonempty) {P} (hP : P ∈ S) : sInf S ≤ P := by
  simpa [← SetLike.coe_subset_coe, hS] using Set.biInter_subset_of_mem hP

theorem le_sInf (hS : S.Nonempty) {P} (hP : ∀ Q ∈ S, P ≤ Q) : P ≤ sInf S := by
  simpa [← SetLike.coe_subset_coe, hS] using Set.subset_iInter₂ hP

end sInf

section sSup

variable [IsSemireal R] {S : Set (RingPreordering R)}

variable (S) in
/-- The union of a directed set of preorderings is a preordering. -/
noncomputable instance : SupSet (RingPreordering R) where
  sSup S := {
    toSubsemiring :=
      open Classical in
      if (DirectedOn (· ≤ ·) S) ∧ S.Nonempty then
        SupSet.sSup (toSubsemiring '' S : Set (Subsemiring R))
      else (⊥ : RingPreordering R).toSubsemiring,
    mem_of_isSquare' {x} hx := by
      split_ifs with h
      · rcases h with ⟨hSd, hSn⟩
        have : DirectedOn (· ≤ ·) (toSubsemiring '' S) := directedOn_image.mpr hSd
        aesop (add simp Subsemiring.mem_sSup_of_directedOn,
                  unsafe forward Set.Nonempty.some_mem)
      · aesop
    neg_one_notMem' := by
      split_ifs with h
      · rcases h with ⟨hSd, hSn⟩
        have : DirectedOn (· ≤ ·) (toSubsemiring '' S) := directedOn_image.mpr hSd
        aesop (add simp Subsemiring.mem_sSup_of_directedOn,
                  unsafe forward Set.Nonempty.some_mem)
      · simpa using IsSemireal.not_isSumSq_neg_one }

@[simp]
theorem sSup_empty : sSup ∅ = (⊥ : RingPreordering R) := by ext; simp [sSup]

@[simp]
theorem sSup_toSubsemiring_of_directedOn (hSd : DirectedOn (· ≤ ·) S) (hS : S.Nonempty) :
    (sSup S).toSubsemiring = SupSet.sSup (RingPreordering.toSubsemiring '' S) := by
  simp [sSup, *]

@[simp, norm_cast]
theorem coe_sSup_of_directedOn (hSd : DirectedOn (· ≤ ·) S) (hS : S.Nonempty) :
    ((sSup S : RingPreordering R) : Set R) = ⋃ P ∈ S, P := by
  simp [sSup, Subsemiring.coe_sSup_of_directedOn (by aesop) <| directedOn_image.mpr hSd, *]

@[simp]
theorem mem_sSup_of_directedOn {hSd : DirectedOn (· ≤ ·) S} {hS : S.Nonempty} {x : R} :
    x ∈ sSup S ↔ ∃ p ∈ S, x ∈ p := by
  simp [← SetLike.mem_coe, *]

noncomputable instance : CompletePartialOrder (RingPreordering R) where
  lubOfDirected S hSd := by
    by_cases hSn : S.Nonempty
    · refine ⟨fun _ hP ↦ ?_, fun _ hP ↦ ?_⟩
      · rw [← SetLike.coe_subset_coe]
        simpa [Set.nonempty_of_mem hP, hSd] using Set.subset_biUnion_of_mem hP
      · rw [← SetLike.coe_subset_coe]
        simpa [hSd, hSn] using Set.iUnion₂_subset hP
    · simp_all [Set.not_nonempty_iff_eq_empty]

@[simp]
theorem supportAddSubgroup_sSup (hSd : DirectedOn (· ≤ ·) S) (hS : S.Nonempty) :
    (sSup S).supportAddSubgroup = SupSet.sSup (supportAddSubgroup '' S) := by
  ext x
  rw [AddSubgroup.mem_sSup_of_directedOn (by simp_all)
       (.mono_comp (fun _ _ h ↦ supportAddSubgroup_mono h) hSd)]
  simp only [mem_supportAddSubgroup, mem_sSup_of_directedOn, Set.mem_image,
    exists_exists_and_eq_and, hSd, hS]
  refine ⟨?_, by aesop⟩
  rintro ⟨⟨_, hs₁, _⟩, ⟨_, hs₂, _⟩⟩
  rcases hSd _ hs₁ _ hs₂ with ⟨s, hs⟩
  exact ⟨s, by aesop⟩

protected theorem HasIdealSupport.sSup (hSd : DirectedOn (· ≤ ·) S) (hS : S.Nonempty)
    (h : ∀ P ∈ S, P.HasIdealSupport) : (sSup S).HasIdealSupport := by
  simp only [hasIdealSupport_iff, mem_sSup_of_directedOn, forall_exists_index, and_imp, *] at *
  rintro x a P hP hP' Q hQ hQ'
  rcases hSd _ hP _ hQ with ⟨R, hR, hPR, hQR⟩
  have := h _ hR x a (hPR hP') (hQR hQ')
  exact ⟨⟨R, hR, this.1⟩, ⟨R, hR, this.2⟩⟩

@[simp]
theorem support_sSup (hSd : DirectedOn (· ≤ ·) S) (hS : S.Nonempty)
    (h : ∀ P ∈ S, P.HasIdealSupport) :
    letI _ := HasIdealSupport.sSup hSd hS h
    (sSup S).support =
    SupSet.sSup {s | ∃ P, ∃ hP : P ∈ S, letI _ := h _ hP; s = P.support} := by
  generalize_proofs
  ext x
  have : x ∈ (sSup S).support ↔ x ∈ SupSet.sSup (supportAddSubgroup '' S) := by
    simp [← supportAddSubgroup_sSup (hS := hS) (hSd := hSd)]
  rw [this,
      AddSubgroup.mem_sSup_of_directedOn (by simp_all)
        (.mono_comp (fun _ _ h ↦ supportAddSubgroup_mono h) hSd),
      Submodule.mem_sSup_of_directed]
  · aesop
  · rcases hS with ⟨P, hP⟩
    exact ⟨let _ := h P hP; P.support, by aesop⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rcases hSd _ hx _ hy with ⟨z, hz, _, _⟩
    let _ := h _ hx
    let _ := h _ hy
    let _ := h _ hz
    exact ⟨z.support, by aesop (add safe apply support_mono)⟩

end sSup

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
    exact ⟨x, by aesop⟩
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
