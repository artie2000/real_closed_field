/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/

import Mathlib.Geometry.Convex.Cone.Pointed
import RealClosedField.Algebra.Group.Submonoid.Support

-- TODO : sync with current work eg #33664
-- TODO : when can `R` be a partial order?

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]

section Module

variable {M : Type*} [AddCommGroup M] [Module R M]

namespace PointedCone

variable (C : PointedCone R M)

@[aesop 50% apply, aesop safe forward (immediate := [hx₁])]
theorem eq_zero_of_mem_of_neg_mem (hC : C.IsPointed) {x : M} (hx₁ : x ∈ C) (hx₂ : -x ∈ C) : x = 0 :=
  C.toAddSubmonoid.eq_zero_of_mem_of_neg_mem hx₁ hx₂

@[aesop safe forward (immediate := [hx₂])]
alias eq_zero_of_mem_of_neg_mem₂ := eq_zero_of_mem_of_neg_mem -- for Aesop

@[aesop safe forward, aesop safe apply]
theorem mem_or_neg_mem (hC : C.IsSpanning) : ∀ a, a ∈ C ∨ -a ∈ C :=
  C.toAddSubmonoid.mem_or_neg_mem

/--
The lineality space of a convex cone over a ring `R` is the biggest `R`-submodule it contains.
-/
def lineal : Submodule R M where
  __ := C.toAddSubmonoid.support
  smul_mem' r _ hx := by
    by_cases hr : 0 ≤ r
    · simpa using And.intro (C.smul_mem hr hx.1) (C.smul_mem hr hx.2) -- TODO : `aesop` lineal for `PointedCone`
    · have hr := le_of_lt <| neg_pos_of_neg <| lt_of_not_ge hr
      simpa using And.intro (C.smul_mem hr hx.2) (C.smul_mem hr hx.1)

variable {S} in
@[aesop simp]
theorem mem_lineal {x} : x ∈ C.lineal ↔ x ∈ C ∧ -x ∈ C := .rfl

theorem coe_lineal : C.lineal = (C : Set M) ∩ -(C : Set M) := rfl

@[simp]
theorem support_eq : C.support = C.lineal.toAddSubgroup := rfl

variable {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
         (f : M →ₗ[R] M')
         (C D : PointedCone R M) (C' : PointedCone R M') {s : Set (PointedCone R M)}

@[simp]
theorem lineal_eq_bot (hC : C.IsPointed) : C.lineal = ⊥ := by
  apply_fun Submodule.toAddSubgroup using Submodule.toAddSubgroup_injective
  simp [← support_eq]

instance [C'.IsSpanning] : (C'.comap f).IsSpanning where

variable {f} in
theorem IsSpanning.map (hC : C.IsSpanning) (hf : Function.Surjective f) : (C.map f).IsSpanning :=
  AddSubmonoid.IsSpanning.map C.toAddSubmonoid (f := f.toAddMonoidHom) hf

theorem IsPointed.of_lineal_eq_bot (h : C.lineal = ⊥) : C.IsPointed where
  eq_zero_of_mem_of_neg_mem {x} := by
    apply_fun (x ∈ ·) at h
    aesop

variable {C D} in
theorem lineal_mono (h : C ≤ D) : C.lineal ≤ D.lineal := fun _ ↦ by aesop

@[simp]
theorem lineal_inf : (C ⊓ D).lineal = C.lineal ⊓ D.lineal := by aesop

@[simp]
theorem lineal_sInf : (sInf s).lineal = InfSet.sInf (lineal '' s) := by aesop

@[simp]
theorem comap_lineal : (C'.comap f).lineal = (C'.lineal).comap f := by
  ext x
  have := C'.toAddSubmonoid.comap_support f.toAddMonoidHom
  apply_fun (x ∈ ·) at this
  simpa [-AddSubmonoid.comap_support]

variable {f C} in
@[simp]
theorem map_lineal (hsupp : f.ker ≤ C.lineal) : (C.map f).lineal = (C.lineal).map f := by
  ext x
  have := AddSubmonoid.map_support (f := f.toAddMonoidHom) hsupp
  apply_fun (x ∈ ·) at this
  simpa

end PointedCone

variable (M)

instance [LinearOrder M] [IsOrderedAddMonoid M] [IsOrderedModule R M] :
    (PointedCone.positive R M).IsSpanning := -- TODO : rename to `nonneg`?
  inferInstanceAs (AddSubmonoid.nonneg M).IsSpanning

instance [PartialOrder M] [IsOrderedAddMonoid M] [IsOrderedModule R M] :
    (PointedCone.positive R M).IsPointed :=
  inferInstanceAs (AddSubmonoid.nonneg M).IsPointed

variable {M} (C : PointedCone R M) (hC : C.IsPointed)

theorem IsOrderedModule.mkOfPointedCone :
    letI _ := PartialOrder.mkOfAddSubmonoid C.toAddSubmonoid
    IsOrderedModule R M :=
  letI _ := PartialOrder.mkOfAddSubmonoid C.toAddSubmonoid
  haveI := IsOrderedAddMonoid.mkOfAddSubmonoid C.toAddSubmonoid
  { smul_le_smul_of_nonneg_left _ hr _ _ hm := by simpa [smul_sub] using C.smul_mem hr hm
    smul_le_smul_of_nonneg_right _ hm r₁ r₂ hr := by
      simpa [sub_smul] using C.smul_mem (r := r₂ - r₁) (by simpa using hr) hm }

namespace Module

variable (R) in
/-- Equivalence between cones with zero lineality space in an `R`-module `M`
    and partially ordered `R`-module structures on `M`. -/
noncomputable def isPointedPartialOrderEquiv :
    Equiv {C : PointedCone R M // C.IsPointed}
          {o : PartialOrder M // IsOrderedAddMonoid M ∧ IsOrderedModule R M} where
  toFun := fun ⟨C, _⟩ => ⟨.mkOfAddSubmonoid C.toAddSubmonoid, .mkOfAddSubmonoid _, .mkOfPointedCone _⟩
  invFun := fun ⟨_, ho⟩ => have := ho.1; have := ho.2; ⟨.positive R M, inferInstance⟩
  left_inv := fun ⟨_, _⟩ => by ext; simp
  right_inv := fun ⟨_, _, _⟩ => by ext; simp

@[simp]
theorem isPointedPartialOrderEquiv_apply
    (C : PointedCone R M) (h : C.IsPointed) :
    isPointedPartialOrderEquiv R ⟨C, h⟩ = PartialOrder.mkOfAddSubmonoid C.toAddSubmonoid := rfl

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
          {o : LinearOrder M // IsOrderedAddMonoid M ∧ IsOrderedModule R M} where
  toFun := fun ⟨C, hC⟩ => have := hC.1; have := hC.2;
    ⟨.mkOfAddSubmonoid C.toAddSubmonoid, .mkOfAddSubmonoid _, .mkOfPointedCone _⟩
  invFun := fun ⟨_, ho⟩ => have := ho.1; have := ho.2
    ⟨.positive R M, by infer_instance, by infer_instance⟩
  left_inv := fun ⟨_, _, _⟩ => by ext; simp
  right_inv := fun ⟨_, _, _⟩ => by ext; simp

open Classical in
@[simp]
theorem isPointedLinearOrderEquiv_apply
    (C : PointedCone R M) (h : C.IsPointed ∧ C.IsSpanning) :
    isPointedLinearOrderEquiv R ⟨C, h⟩ =
    have := h.1; have := h.2; LinearOrder.mkOfAddSubmonoid C.toAddSubmonoid := rfl

@[simp]
theorem isPointedLinearOrderEquiv_symm_apply (o : LinearOrder M)
    (h : IsOrderedAddMonoid M ∧ IsOrderedModule R M) :
    have := h.1; have := h.2
    (isPointedLinearOrderEquiv R).symm ⟨o, h⟩ = PointedCone.positive R M := rfl

end Module
