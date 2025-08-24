/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib

/- Lemmas that should be upstreamed to Mathlib -/

open Polynomial in
theorem X_sq_sub_C_irreducible_iff_not_isSquare {F : Type*} [Field F] (a : F) :
    Irreducible (X ^ 2 - C a) ↔ ¬ IsSquare a := by
  rw [isSquare_iff_exists_sq, X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two]
  grind only

-- TODO : generalise to IsAdjoinRoot

attribute [-simp] AdjoinRoot.algebraMap_eq

namespace AdjoinRoot.Quadratic

open _root_.Polynomial

set_option quotPrecheck false in
scoped notation3 "|" K "[√" a "]" => AdjoinRoot (X ^ 2 - C a : K[X])

set_option quotPrecheck false in
scoped notation3 "√" a => root (X ^ 2 - C a)

variable {K : Type*} [Field K] {a : K} (ha : ¬ IsSquare a)

-- this should just be the default coercion
set_option quotPrecheck false in
scoped notation "of" => algebraMap K |K[√a]

@[simp]
theorem sq_root : (√a) ^ 2 = of a := by
  suffices (√a) ^ 2 - of a = 0 by
    linear_combination this
  have := eval₂_root (X ^ 2 - C a)
  simpa

noncomputable def basis : Module.Basis (Fin 2) K |K[√a] :=
  have nz : X ^ 2 - C a ≠ 0 := fun _ ↦ by simp_all [← X_sq_sub_C_irreducible_iff_not_isSquare]
  (powerBasis nz).basis.reindex <| finCongr <|
    show (powerBasis nz).dim = 2 by simp

include ha in
theorem isQuadraticExtension : Algebra.IsQuadraticExtension K |K[√a] where
  finrank_eq_two' := by simp [Module.finrank_eq_nat_card_basis (basis ha)]

@[simp]
theorem coe_basis (i : Fin 2) :
  basis ha i = (√a) ^ (i : ℕ) := by
    simp [-powerBasis_dim, basis]

theorem basis_0 : basis ha 0 = 1 := by simp

theorem basis_1 : basis ha 1 = √a := by simp

@[simp]
theorem repr_1 : (basis ha).repr 1 = Finsupp.single 0 1 := by
  rw [← basis_0, Module.Basis.repr_self]

@[simp]
theorem repr_root : (basis ha).repr (√a) = Finsupp.single 1 1 := by
  rw [← basis_1, Module.Basis.repr_self]

-- PRed as change to Module.Basis.repr_algebraMap
theorem _root_.Module.Basis.repr_algebraMap'
    {R : Type*} {S : Type*} [CommRing R] [Ring S] [Algebra R S]
    {ι : Type*} [DecidableEq ι] {B : Module.Basis ι R S} {i : ι} (hBi : B i = 1)
    (r : R) : B.repr ((algebraMap R S) r) = Finsupp.single i r := by
  ext j; simp [Algebra.algebraMap_eq_smul_one, ← hBi]

--TODO: generalise next two results to any PowerBasis?

@[simp]
theorem repr_algebraMap {x} : (basis ha).repr (of x) = Finsupp.single 0 x :=
  Module.Basis.repr_algebraMap' (basis_0 ha) x

@[simp]
theorem repr_ofNat {n : ℕ} [Nat.AtLeastTwo n] :
    (basis ha).repr ofNat(n) = Finsupp.single 0 (n : K) :=
  Module.Basis.repr_algebraMap' (basis_0 ha) ofNat(n)

theorem self_eq_basis (x) :
    x = of ((basis ha).repr x 0) + of ((basis ha).repr x 1) * √a := by
  nth_rw 1 [← (basis ha).sum_repr x]
  simp [Algebra.smul_def]

theorem repr_of_add_of_mul_root {x y} :
    (basis ha).repr (of x + of y * √a) = fun₀ | 0 => x
                                              | 1 => y := by
  ext i; fin_cases i <;> simp [Module.Basis.repr_smul']

@[simp]
theorem repr_basis_mul (x y) : (basis ha).repr (x * y) =
    fun₀
    | 0 => (basis ha).repr x 0 * (basis ha).repr y 0 +
                a * (basis ha).repr x 1 * (basis ha).repr y 1
    | 1 => (basis ha).repr x 0 * (basis ha).repr y 1 +
                (basis ha).repr y 0 * (basis ha).repr x 1 := by
  rw [← repr_of_add_of_mul_root ha]
  congr
  nth_rw 1 [self_eq_basis ha x, self_eq_basis ha y]
  ring_nf
  simp only [sq_root, map_mul, map_add]
  ring

end AdjoinRoot.Quadratic
