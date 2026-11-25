/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/

import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Algebra.Group.Submonoid.Support
import Mathlib.Algebra.Order.Group.Cone

variable {R M : Type*}

namespace PointedCone

section support

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  {C : PointedCone R M}

theorem mem_support {x : M} : x ∈ C.support ↔ x ∈ C ∧ -x ∈ C := by simp

theorem isPointed_def : C.IsPointed ↔ ∀ {x}, x ∈ C → -x ∈ C → x = 0 := by
  simp [AddSubmonoid.IsPointed]

theorem isSpanning_def : C.IsSpanning ↔ ∀ a, a ∈ C ∨ -a ∈ C := by simp [AddSubmonoid.IsSpanning]

variable {M' : Type*} [AddCommGroup M'] [Module R M']
  (f : M →ₗ[R] M') (C D : PointedCone R M) (C' : PointedCone R M') {s : Set (PointedCone R M)}

theorem comap_isSpanning (hC' : C'.IsSpanning) : (C'.comap f).IsSpanning :=
  hC'.comap (f := f.toAddMonoidHom)

variable {f} in
theorem map_isSpanning (hC : C.IsSpanning) (hf : Function.Surjective f) : (C.map f).IsSpanning :=
  hC.map (f := f.toAddMonoidHom) hf

end support

section lineal

variable [Ring R] [LinearOrder R] [IsOrderedRing R]

-- TODO : switch to galois connection proofs

variable {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
         (f : M →ₗ[R] M')
         (C D : PointedCone R M) (C' : PointedCone R M') {s : Set (PointedCone R M)}

-- TODO : reverse direction of the simp lemma `PointedCone.support_eq`
@[simp]
theorem lineal_eq_bot (hC : C.IsPointed) : C.lineal = ⊥ := by
  apply_fun Submodule.toAddSubgroup using Submodule.toAddSubgroup_injective
  simpa [← support_eq] using hC.support_eq_bot

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

end lineal

end PointedCone

section Order

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]

-- TODO : rename `PointedCone.positive` to `PointedCone.nonneg`

variable (M) in
theorem PointedCone.IsSpanning.positive
    [LinearOrder M] [IsOrderedAddMonoid M] [IsOrderedModule R M] :
    (PointedCone.positive R M).IsSpanning := .nonneg M

variable (M) in
theorem PointedCone.IsPointed.positive
    [PartialOrder M] [IsOrderedAddMonoid M] [IsOrderedModule R M] :
    (PointedCone.positive R M).IsPointed := .nonneg M

variable [IsOrderedCancelAddMonoid R] [ExistsAddOfLE R]

theorem IsOrderedModule.ofPointedCone
    {C : PointedCone R M} (hC : C.IsPointed) :
    letI _ := PartialOrder.ofAddSubmonoid hC
    IsOrderedModule R M :=
  letI _ := PartialOrder.ofAddSubmonoid hC
  { smul_le_smul_of_nonneg_left _ hr _ _ hm := by simpa [smul_sub] using C.smul_mem hr hm
    smul_le_smul_of_nonneg_right _ hm r₁ r₂ hr := by
      rcases exists_add_of_le hr with ⟨r, rfl⟩
      simpa [add_smul] using C.smul_mem (r := r) (by simpa using hr) hm }

namespace Module

variable (R) in
/-- Equivalence between cones with zero lineality space in an `R`-module `M`
    and partially ordered `R`-module structures on `M`. -/
noncomputable def isPointedPartialOrderEquiv :
    Equiv {C : PointedCone R M // C.IsPointed}
          {_o : PartialOrder M // IsOrderedAddMonoid M ∧ IsOrderedModule R M} where
  toFun := fun ⟨_, hC⟩ ↦ ⟨.ofAddSubmonoid hC, .ofAddSubmonoid _, .ofPointedCone _⟩
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
    ⟨.ofAddSubmonoid hC.1 hC.2, .ofAddSubmonoid _, .ofPointedCone _⟩
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

end Order
