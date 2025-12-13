
/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import RealClosedField.Algebra.Order.Cone.Order
import RealClosedField.Algebra.Order.Ring.Ordering.Defs
import RealClosedField.Algebra.Ring.Semireal.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!

We prove basic properties of orderings on rings, and show that they are preserved
under certain operations.

## References

- [*An introduction to real algebra*, T.Y. Lam][lam_1984]

-/

namespace Subsemiring

section Ring

variable {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (P : Subsemiring R) (P' : Subsemiring S)

namespace IsPreordering

variable [P.IsPreordering]

variable {P} in
@[aesop unsafe 90% apply (rule_sets := [SetLike])]
theorem unitsInv_mem {a : Rˣ} (ha : ↑a ∈ P) : ↑a⁻¹ ∈ P := by
  have : (a * (a⁻¹ * a⁻¹) : R) ∈ P := by aesop (config := { enableSimp := false })
  simp_all

theorem one_notMem_supportAddSubgroup : 1 ∉ P.supportAddSubgroup :=
  fun h => P.neg_one_notMem h.2

theorem one_notMem_support [P.HasIdealSupport] : 1 ∉ P.support := by
  simpa using one_notMem_supportAddSubgroup P

theorem supportAddSubgroup_ne_top : P.supportAddSubgroup ≠ ⊤ :=
  fun h => one_notMem_supportAddSubgroup P (by simp [h])

theorem support_ne_top [P.HasIdealSupport] : P.support ≠ ⊤ := by
  apply_fun Submodule.toAddSubgroup
  simpa using supportAddSubgroup_ne_top P

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
    have : P.HasMemOrNegMem := ⟨by simp [h]⟩
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

variable {P} in
theorem of_le {Q : Subsemiring R} (hPQ : P ≤ Q) (hQ : -1 ∉ Q) : Q.IsPreordering where

end IsPreordering

instance [Nontrivial R] [P.HasMemOrNegMem] [P.IsCone] : P.IsPreordering :=
  .of_support_neq_top (by simp)

instance [IsDomain R] [P.HasMemOrNegMem] [P.IsCone] : P.IsOrdering where
  __ : P.support.IsPrime := by simpa using Ideal.bot_prime

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

instance [P'.IsOrdering] : IsOrdering (P'.comap f) where
  __ : (P'.comap f).HasMemOrNegMem := by
    simpa using (inferInstance : (P'.toAddSubmonoid.comap f.toAddMonoidHom).HasMemOrNegMem)
  __ : (P'.comap f).support.IsPrime := by
    simpa [-RingHom.toAddMonoidHom_eq_coe] using
      (inferInstance : (Ideal.comap f P'.toAddSubmonoid.support).IsPrime)

instance [P'.IsPreordering] : (P'.comap f).IsPreordering where

variable {f P} in
theorem IsOrdering.map [P.IsOrdering] (hf : Function.Surjective f)
    (hsupp : RingHom.ker f ≤ P.support) : IsOrdering (P.map f) where
  __ : (P.map f).HasMemOrNegMem := by
    simpa using AddSubmonoid.HasMemOrNegMem.map P.toAddSubmonoid (f := f.toAddMonoidHom) hf
  __ : (P.map f).support.IsPrime := by
    have := AddSubmonoid.map_support hf hsupp
    simp at this
    simpa [this] using Ideal.map_isPrime_of_surjective hf hsupp

variable {f P} in
theorem IsPreordering.map [P.IsPreordering] (hf : Function.Surjective f)
    (hsupp : f.toAddMonoidHom.ker ≤ P.supportAddSubgroup) : (P.map f).IsPreordering where
  mem_of_isSquare hx := by
    rcases isSquare_subset_image_isSquare hf hx with ⟨x, hx, hfx⟩
    exact ⟨x, by aesop⟩
  neg_one_notMem := fun ⟨x', hx', _⟩ => by
    have : -(x' + 1) + x' ∈ P := add_mem (hsupp (show f (x' + 1) = 0 by simp_all)).2 hx'
    aesop

end Ring

section CommRing

variable {R : Type*} [CommRing R] (P : Subsemiring R)

namespace IsPreordering

variable [P.IsPreordering]

-- TODO : generalise to noncomm rings by doing the algebra manually?
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

end IsPreordering

theorem IsPreordering.ofIsCone [Nontrivial R] [P.IsCone] (h : .sumSq R ≤ P) : P.IsPreordering where

instance [IsSemireal R] : (sumSq R).IsPreordering where
  neg_one_notMem := by simpa using IsSemireal.not_isSumSq_neg_one

theorem _root_.isSemireal_ofIsPreordering [P.IsPreordering] : IsSemireal R :=
  .of_not_isSumSq_neg_one (P.neg_one_notMem <| P.mem_of_isSumSq ·)

theorem _root_.exists_isPreordering_iff_isSemireal :
    (∃ P : Subsemiring R, P.IsPreordering) ↔ IsSemireal R where
  mp | ⟨P, _⟩ => isSemireal_ofIsPreordering P
  mpr _ := ⟨sumSq R, inferInstance⟩

end CommRing

section Field

variable {F : Type*} [Field F]

namespace IsPreordering

variable (P : Subsemiring F) [P.IsPreordering]

variable {P} in
@[aesop unsafe 90% apply (rule_sets := [SetLike])]
theorem inv_mem {a : F} (ha : a ∈ P) : a⁻¹ ∈ P := by
  have mem : a * (a⁻¹ * a⁻¹) ∈ P := by aesop
  field_simp at mem
  simp_all

instance : P.IsCone := AddSubmonoid.isCone_iff.mpr fun x _ _ ↦ by
  by_contra
  have mem : -x * x⁻¹ ∈ P := by aesop (erase simp neg_mul)
  field_simp at mem
  exact P.neg_one_notMem mem

instance : P.support.IsPrime := by simpa using Ideal.bot_prime

end IsPreordering

variable (F) in
open Classical in
noncomputable def ringOrderingLinearOrderEquiv :
    Equiv {O : Subsemiring F // O.IsOrdering}
          {l : LinearOrder F // IsStrictOrderedRing F} where
  toFun := fun ⟨O, hO⟩ =>
    let ⟨l, hl⟩ := Ring.isConeLinearOrderEquiv F ⟨O, inferInstance, inferInstance⟩
    ⟨l, IsOrderedRing.toIsStrictOrderedRing F⟩
  invFun := fun ⟨l, hl⟩ =>
    let ⟨O, hO⟩ := (Ring.isConeLinearOrderEquiv F).symm ⟨l, inferInstance⟩
    have := hO.1; have := hO.2; ⟨O, inferInstance⟩
  left_inv := fun ⟨_, _⟩ => by ext; simp
  right_inv := fun ⟨_, _⟩ => by ext; simp

@[simp]
theorem ringOrderingLinearOrderEquiv_apply (O : Subsemiring F) (h : O.IsOrdering) :
    (ringOrderingLinearOrderEquiv F ⟨O, h⟩ : LinearOrder F) =
    Ring.isConeLinearOrderEquiv F ⟨O, inferInstance, inferInstance⟩ := by
  simp [ringOrderingLinearOrderEquiv]

@[simp]
theorem ringOrderingLinearOrderEquiv_symm_apply_val
    (l : LinearOrder F) (h : IsStrictOrderedRing F) :
    ((ringOrderingLinearOrderEquiv F).symm ⟨l, h⟩ : Subsemiring F) =
    (Ring.isConeLinearOrderEquiv F).symm ⟨l, inferInstance⟩ := by
  simp [ringOrderingLinearOrderEquiv]

end Field

end Subsemiring
