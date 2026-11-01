/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/

import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Algebra.Group.Submonoid.Support
import Mathlib.Algebra.Order.Group.Cone

-- TODO : sync with current work eg #33664
-- TODO : when can `R` be a partial order?

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]

section Module

variable {M : Type*} [AddCommGroup M] [Module R M]

namespace PointedCone

variable {C : PointedCone R M}

-- TODO : lemmas like for subsemiring

@[aesop 50% apply, aesop safe forward (immediate := [hx₁])]
theorem eq_zero_of_mem_of_neg_mem (hC : C.IsPointed) {x : M} (hx₁ : x ∈ C) (hx₂ : -x ∈ C) : x = 0 :=
  hC.eq_zero_of_mem_of_neg_mem hx₁ hx₂

@[aesop safe forward (immediate := [hx₂])]
alias eq_zero_of_mem_of_neg_mem₂ := eq_zero_of_mem_of_neg_mem -- for Aesop

@[aesop safe forward, aesop safe apply]
theorem mem_or_neg_mem (hC : C.IsSpanning) : ∀ a, a ∈ C ∨ -a ∈ C := hC.mem_or_neg_mem

variable {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
         (f : M →ₗ[R] M')
         (C D : PointedCone R M) (C' : PointedCone R M') {s : Set (PointedCone R M)}

-- TODO : reverse direction of the simp lemma `PointedCone.support_eq`
@[simp]
theorem lineal_eq_bot (hC : C.IsPointed) : C.lineal = ⊥ := by
  apply_fun Submodule.toAddSubgroup using Submodule.toAddSubgroup_injective
  simpa [← support_eq] using hC.support_eq_bot

theorem comap_isSpanning (hC' : C'.IsSpanning) : (C'.comap f).IsSpanning :=
  hC'.comap (f := f.toAddMonoidHom)

variable {f} in
theorem map_isSpanning (hC : C.IsSpanning) (hf : Function.Surjective f) : (C.map f).IsSpanning :=
  hC.map (f := f.toAddMonoidHom) hf

theorem _root_.AddSubmonoid.IsPointed.of_lineal_eq_bot (h : C.lineal = ⊥) : C.IsPointed :=
  fun x _ _ ↦ by
    apply_fun (x ∈ ·) at h
    simp_all

variable {C D} in
theorem lineal_mono (h : C ≤ D) : C.lineal ≤ D.lineal := fun _ ↦ by aesop

@[simp]
theorem lineal_inf : (C ⊓ D).lineal = C.lineal ⊓ D.lineal := by aesop

@[simp]
theorem lineal_sInf : (sInf s).lineal = InfSet.sInf (lineal '' s) := by aesop

@[simp]
theorem lineal_comap : (C'.comap f).lineal = (C'.lineal).comap f := by ext; simp

variable {f C} in
@[simp]
theorem lineal_map (hsupp : f.ker ≤ C.lineal) : (C.map f).lineal = (C.lineal).map f := by
  ext x
  have := AddSubmonoid.support_map (f := f.toAddMonoidHom) hsupp
  apply_fun (x ∈ ·) at this
  simpa

end PointedCone

variable (M)

-- TODO : rename `positive` to `nonneg`?
theorem PointedCone.IsSpanning.positive
    [LinearOrder M] [IsOrderedAddMonoid M] [IsOrderedModule R M] :
    (PointedCone.positive R M).IsSpanning := .nonneg M

theorem PointedCone.IsPointed.positive
    [PartialOrder M] [IsOrderedAddMonoid M] [IsOrderedModule R M] :
    (PointedCone.positive R M).IsPointed := .nonneg M

variable {M} {C : PointedCone R M} (hC : C.IsPointed)

theorem IsOrderedModule.ofAddSubmonoid :
    letI _ := PartialOrder.ofAddSubmonoid hC
    IsOrderedModule R M :=
  letI _ := PartialOrder.ofAddSubmonoid hC
  haveI := IsOrderedAddMonoid.ofAddSubmonoid hC
  { smul_le_smul_of_nonneg_left _ hr _ _ hm := by simpa [smul_sub] using C.smul_mem hr hm
    smul_le_smul_of_nonneg_right _ hm r₁ r₂ hr := by
      simpa [sub_smul] using C.smul_mem (r := r₂ - r₁) (by simpa using hr) hm }

namespace Module

variable (R) in
/-- Equivalence between cones with zero lineality space in an `R`-module `M`
    and partially ordered `R`-module structures on `M`. -/
noncomputable def isPointedPartialOrderEquiv :
    Equiv {C : PointedCone R M // C.IsPointed}
          {_o : PartialOrder M // IsOrderedAddMonoid M ∧ IsOrderedModule R M} where
  toFun := fun ⟨_, hC⟩ ↦ ⟨.ofAddSubmonoid hC, .ofAddSubmonoid _, .ofAddSubmonoid _⟩
  invFun := fun ⟨_, ⟨_, _⟩⟩ ↦ ⟨.positive R M, PointedCone.IsPointed.positive _⟩
  left_inv := fun ⟨_, _⟩ ↦ by ext; simp
  right_inv := fun ⟨_, _, _⟩ ↦ by ext; simp +instances

@[simp]
theorem isPointedPartialOrderEquiv_apply
    (C : PointedCone R M) (h : C.IsPointed) :
    isPointedPartialOrderEquiv R ⟨C, h⟩ = PartialOrder.ofAddSubmonoid h := rfl

@[simp]
theorem isPointedPartialOrderEquiv_symm_apply (o : PartialOrder M)
    (h : IsOrderedAddMonoid M ∧ IsOrderedModule R M) :
    have := h.1; have := h.2
    (isPointedPartialOrderEquiv R).symm ⟨o, h⟩ = ConvexCone.positive R M := rfl

variable (R) in
open Classical in
/-- Equivalence between maximal cones with zero lineality space in an `R`-module `M`
    and linearly ordered `R`-module structures on `M`. -/
noncomputable def isPointedLinearOrderEquiv :
    Equiv {C : PointedCone R M // C.IsPointed ∧ C.IsSpanning}
          {_o : LinearOrder M // IsOrderedAddMonoid M ∧ IsOrderedModule R M} where
  toFun := fun ⟨C, hC⟩ ↦
    ⟨.ofAddSubmonoid hC.1 hC.2, .ofAddSubmonoid _, .ofAddSubmonoid _⟩
  invFun := fun ⟨_, ⟨_, _⟩⟩ ↦
    ⟨.positive R M, PointedCone.IsPointed.positive _, PointedCone.IsSpanning.positive _⟩
  left_inv := fun ⟨_, _, _⟩ ↦ by ext; simp
  right_inv := fun ⟨_, _, _⟩ ↦ by ext; simp

open Classical in
@[simp]
theorem isPointedLinearOrderEquiv_apply
    (C : PointedCone R M) (h : C.IsPointed ∧ C.IsSpanning) :
    isPointedLinearOrderEquiv R ⟨C, h⟩ = LinearOrder.ofAddSubmonoid h.1 h.2 := rfl

@[simp]
theorem isPointedLinearOrderEquiv_symm_apply (o : LinearOrder M)
    (h : IsOrderedAddMonoid M ∧ IsOrderedModule R M) :
    have := h.1; have := h.2
    (isPointedLinearOrderEquiv R).symm ⟨o, h⟩ = PointedCone.positive R M := rfl

end Module
