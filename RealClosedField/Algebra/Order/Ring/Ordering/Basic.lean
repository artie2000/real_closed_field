/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Ring.Semireal.Defs
import RealClosedField.Algebra.Order.Ring.Ordering.Defs

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

@[mono]
theorem toSubsemiring_strictMono : StrictMono (toSubsemiring : RingPreordering R → _) :=
  fun _ _ => id

theorem toSubsemiring_le {P₁ P₂ : RingPreordering R} :
    P₁.toSubsemiring ≤ P₂.toSubsemiring ↔ P₁ ≤ P₂ := .rfl

@[mono]
theorem toSubsemiring_mono : Monotone (toSubsemiring : RingPreordering R → _) :=
  toSubsemiring_strictMono.monotone

@[aesop unsafe 80% (rule_sets := [SetLike])]
theorem neg_mul_mem_of_mem {x y : R} (hx : x ∈ P) (hy : -y ∈ P) : -(x * y) ∈ P := by
  simpa using mul_mem hx hy

@[aesop unsafe 80% (rule_sets := [SetLike])]
theorem neg_mul_mem_of_neg_mem {x y : R} (hx : -x ∈ P) (hy : y ∈ P) : -(x * y) ∈ P := by
  simpa using mul_mem hx hy

@[aesop unsafe 90% apply (rule_sets := [SetLike])]
theorem inv_mem {a : Rˣ} (ha : ↑a ∈ P) : ↑a⁻¹ ∈ P := by
  rw [show (↑a⁻¹ : R) = a * (a⁻¹ * a⁻¹) by simp]
  aesop (config := { enableSimp := false })

@[aesop unsafe 90% apply (rule_sets := [SetLike])]
theorem Field.inv_mem {F : Type*} [Field F] {P : RingPreordering F} {a : F} (ha : a ∈ P) :
    a⁻¹ ∈ P := by
  rw [show a⁻¹ = a * (a⁻¹ * a⁻¹) by field_simp]
  aesop

@[aesop unsafe 80% apply (rule_sets := [SetLike])]
theorem mem_of_isSumSq {x : R} (hx : IsSumSq x) : x ∈ P := by
  induction hx using IsSumSq.rec' <;> aesop

section mkOfSubsemiring
variable {R : Type*} [CommRing R] {P : Subsemiring R}
  {le : Subsemiring.sumSq R ≤ P} {minus : -1 ∉ P}

/- Construct a preordering from a subsemiring. -/
def mkOfSubsemiring {R : Type*} [CommRing R] (P : Subsemiring R)
    (le : Subsemiring.sumSq R ≤ P) (minus : -1 ∉ P) :
    RingPreordering R where
  toSubsemiring := P
  mem_of_isSquare' hx := by aesop
  neg_one_notMem' := minus

@[simp]
theorem mkOfSubsemiring_toSubsemiring : (mkOfSubsemiring P le minus).toSubsemiring = P := rfl
@[simp] theorem mem_mkOfSubsemiring {x : R} : x ∈ mkOfSubsemiring P le minus ↔ x ∈ P := .rfl
@[simp] theorem coe_mkOfSubsemiring {minus} : mkOfSubsemiring P le minus = (P : Set R) := rfl

end mkOfSubsemiring

section mk'
variable {R : Type*} [CommRing R] {P : Set R} {add} {mul} {sq} {minus}

/- Construct a preordering from a minimal set of axioms. -/
def mk' {R : Type*} [CommRing R] (P : Set R)
    (add   : ∀ {x y : R}, x ∈ P → y ∈ P → x + y ∈ P)
    (mul   : ∀ {x y : R}, x ∈ P → y ∈ P → x * y ∈ P)
    (sq    : ∀ x : R, x * x ∈ P)
    (minus : -1 ∉ P) :
    RingPreordering R where
  carrier := P
  add_mem' {x y} := by simpa using add
  mul_mem' {x y} := by simpa using mul
  mem_of_isSquare' hx := by rcases hx with ⟨y, hy⟩; aesop
  neg_one_notMem' := by simpa using minus
  zero_mem' := by simpa using sq 0
  one_mem' := by simpa using sq 1

@[simp] theorem mem_mk' {x : R} : x ∈ mk' P add mul sq minus ↔ x ∈ P := .rfl
@[simp, norm_cast] theorem coe_mk' {minus} : mk' P add mul sq minus = P := rfl

end mk'

variable (P) in
theorem one_not_mem_supportAddSubgroup : 1 ∉ supportAddSubgroup P := by aesop

variable (P) in
theorem supportAddSubgroup_neq_top : supportAddSubgroup P ≠ ⊤ := fun eq => by
  have : 1 ∉ (⊤ : AddSubgroup R) := by rw[← eq]; exact one_not_mem_supportAddSubgroup P
  simp_all

variable (P) in
theorem one_not_mem_support [HasIdealSupport P] : 1 ∉ support P := one_not_mem_supportAddSubgroup P

variable (P) in
theorem support_neq_top [HasIdealSupport P] : support P ≠ ⊤ := fun eq => by
  apply_fun Submodule.toAddSubgroup at eq
  simpa using supportAddSubgroup_neq_top P eq

namespace HasIdealSupport

theorem smul_mem [HasIdealSupport P]
  (x : R) {a : R} (h₁a : a ∈ P) (h₂a : -a ∈ P) : x * a ∈ P := by
  have := smul_mem_support P
  simp_all

theorem neg_smul_mem [HasIdealSupport P]
  (x : R) {a : R} (h₁a : a ∈ P) (h₂a : -a ∈ P) : -(x * a) ∈ P := by
  have := smul_mem_support P
  simp_all

end HasIdealSupport

theorem hasIdealSupport_of_isUnit_2 (isUnit_2 : IsUnit (2 : R)) : HasIdealSupport P :=
  hasIdealSupport <| fun x a h₁a h₂a => by
  obtain ⟨half, h2⟩ := IsUnit.exists_left_inv isUnit_2
  let y := (1 + x) * half
  let z := (1 - x) * half
  have mem : (y * y) * a + (z * z) * (-a) ∈ P ∧ (y * y) * (-a) + (z * z) * a ∈ P := by aesop
  rw [show x = y * y - z * z by linear_combination (-(2 * x * half) - 1 * x) * h2]
  ring_nf at mem ⊢
  assumption

@[simp]
theorem support_eq_bot {F : Type*} [Field F] (P : RingPreordering F) :
    supportAddSubgroup P = ⊥ := by
  refine AddSubgroup.ext <| fun x => ⟨fun h => ?_, fun h => by aesop⟩
  by_contra hz
  apply RingPreordering.neg_one_notMem P
  rw [show -1 = -x * x⁻¹ by field_simp [show x ≠ 0 by simp_all]]
  aesop (erase simp neg_mul)

@[aesop unsafe 70% apply]
protected theorem eq_zero_of_mem_of_neg_mem {F : Type*} [Field F] {P : RingPreordering F}
    {x} (h : x ∈ P) (h2 : -x ∈ P) : x = 0 := by
  have : (x ∈ supportAddSubgroup P) ↔ (x ∈ (⊥ : AddSubgroup F)) := by rw [support_eq_bot P]
  simp_all [- support_eq_bot]

/-!
### (Prime) orderings
-/

section HasMemOrNegMem

variable [HasMemOrNegMem P]

@[aesop unsafe 70% apply]
theorem neg_mem_of_not_mem (x : R) (h : x ∉ P) : -x ∈ P := by
  have := mem_or_neg_mem P x
  simp_all

@[aesop unsafe 70% apply]
theorem mem_of_not_neg_mem (x : R) (h : -x ∉ P) : x ∈ P := by
  have := mem_or_neg_mem P x
  simp_all

instance : HasIdealSupport P where
  smul_mem_support x a ha := by
    cases mem_or_neg_mem P x with
    | inl => aesop
    | inr hx => simpa using ⟨by simpa using mul_mem hx ha.2, by simpa using mul_mem hx ha.1⟩

end HasMemOrNegMem

instance [IsOrdering P] : (support P).IsPrime where
  ne_top' h := RingPreordering.neg_one_notMem P (by aesop : 1 ∈ support P).2
  mem_or_mem' := IsOrdering.mem_or_mem

instance [HasMemOrNegMem P] [(support P).IsPrime] : IsOrdering P where
  mem_or_neg_mem := mem_or_neg_mem P
  mem_or_mem := Ideal.IsPrime.mem_or_mem (by assumption)

theorem isOrdering_iff :
    IsOrdering P ↔ (∀ a b : R, -(a * b) ∈ P → a ∈ P ∨ b ∈ P) := by
  refine ⟨fun prime a b h₁ => ?_, fun h => ?_⟩
  · by_contra
    have : a * b ∈ P := by simpa using mul_mem (by aesop : -a ∈ P) (by aesop : -b ∈ P)
    have : a ∈ support P ∨ b ∈ support P :=
      Ideal.IsPrime.mem_or_mem inferInstance (by simp_all)
    simp_all
  · exact {(⟨by aesop⟩ : HasMemOrNegMem _) with
      mem_or_mem := fun {x y} hxy => by
        by_contra
        cases (by aesop : x ∈ P ∨ -x ∈ P) with
        | inl =>  have := h (-x) y
                  have := h (-x) (-y)
                  simp_all
        | inr =>  have := h x y
                  have := h x (-y)
                  simp_all }

/-! ## Order operations -/

section Inf
variable {P₁ P₂ : RingPreordering R}

instance : Min (RingPreordering R) where
  min P₁ P₂ := .mkOfSubsemiring (min P₁.toSubsemiring P₂.toSubsemiring)
    (fun _ => by aesop) (by aesop)

@[simp]
theorem inf_toSubsemiring : (P₁ ⊓ P₂).toSubsemiring = P₁.toSubsemiring ⊓ P₂.toSubsemiring := rfl
@[simp] theorem mem_inf {x : R} : x ∈ P₁ ⊓ P₂ ↔ x ∈ P₁ ∧ x ∈ P₂ := .rfl
@[simp, norm_cast] theorem coe_inf : ↑(P₁ ⊓ P₂) = (P₁ ∩ P₂ : Set R) := rfl

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
  bot := .mkOfSubsemiring (Subsemiring.sumSq R) (by aesop)
    (by simpa using IsSemireal.not_isSumSq_neg_one)

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

/- TODO : generalise bundled "→+*" to class instances -/

/-- The preimage of a preordering along a ring homomorphism is a preordering. -/
def comap (f : A →+* B) (P : RingPreordering B) : RingPreordering A where
  __ := P.toSubsemiring.comap f
  mem_of_isSquare' := by aesop (add unsafe apply IsSquare.map) /- TODO : remove add .. once change is merged -/
  neg_one_notMem' := by aesop

@[simp]
theorem coe_comap (P : RingPreordering B) {f : A →+* B} : (P.comap f : Set A) = f ⁻¹' P := rfl

@[simp]
theorem mem_comap {P : RingPreordering B} {f : A →+* B} {x : A} : x ∈ P.comap f ↔ f x ∈ P :=
  .rfl

theorem comap_comap (P : RingPreordering C) (g : B →+* C) (f : A →+* B) :
    (P.comap g).comap f = P.comap (g.comp f) := rfl

/-- The preimage of an ordering along a ring homomorphism is an ordering. -/
instance (P : RingPreordering B) [HasMemOrNegMem P] (f : A →+* B) : HasMemOrNegMem (comap f P) where
  mem_or_neg_mem x := by have := mem_or_neg_mem P (f x); aesop

@[simp]
theorem mem_comap_supportAddSubgroup {P : RingPreordering B} {f : A →+* B} {x : A} :
    x ∈ supportAddSubgroup (P.comap f) ↔ f x ∈ supportAddSubgroup P := by simp

@[simp]
theorem comap_supportAddSubgroup {P : RingPreordering B} {f : A →+* B} :
    supportAddSubgroup (P.comap f) = (supportAddSubgroup P).comap f := by ext; simp

instance (P : RingPreordering B) [HasIdealSupport P] (f : A →+* B) :
    HasIdealSupport (P.comap f) where
  smul_mem_support x a ha := by have := smul_mem_support P (f x) (by simpa using ha); simp_all

@[simp]
theorem mem_comap_support {P : RingPreordering B} [HasIdealSupport P] {f : A →+* B} {x : A} :
    x ∈ support (P.comap f) ↔ f x ∈ support P := by simp

@[simp]
theorem comap_support {P : RingPreordering B} [HasIdealSupport P] {f : A →+* B} :
    support (P.comap f) = (support P).comap f := by ext; simp

/-- The preimage of a prime ordering along a ring homomorphism is a prime ordering. -/
instance (P : RingPreordering B) [IsOrdering P] (f : A →+* B) :
    IsOrdering (comap f P) := by
  have : (support (P.comap f)).IsPrime := by rw [comap_support]; infer_instance
  infer_instance

/-! ## map -/

/-- The image of a preordering `P` along a surjective ring homomorphism
  with kernel contained in the support of `P` is a preordering. -/
def map {f : A →+* B} {P : RingPreordering A} (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ supportAddSubgroup P) : RingPreordering B where
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
    (hsupp : (RingHom.ker f : Set A) ⊆ supportAddSubgroup P) :
    (map hf hsupp : Set B) = f '' P := rfl

@[simp]
theorem mem_map {f : A →+* B} {P : RingPreordering A} (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ supportAddSubgroup P) {y} :
    y ∈ map hf hsupp ↔ ∃ x ∈ P, f x = y := .rfl

/-- The image of an ordering `P` along a surjective ring homomorphism
  with kernel contained in the support of `P` is an ordering. -/
instance {f : A →+* B} {P : RingPreordering A} [HasMemOrNegMem P] (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ supportAddSubgroup P) : HasMemOrNegMem (map hf hsupp) where
  mem_or_neg_mem x := by
    obtain ⟨x', rfl⟩ := hf x
    have := mem_or_neg_mem P x'
    aesop

@[simp↓]
theorem mem_map_supportAddSubgroup {f : A →+* B} {P : RingPreordering A}
    {hf : Function.Surjective f} {hsupp : (RingHom.ker f : Set A) ⊆ supportAddSubgroup P} {x : B} :
    x ∈ supportAddSubgroup (map hf hsupp) ↔ ∃ y ∈ supportAddSubgroup P, f y = x := by
  refine ⟨fun ⟨⟨a, ⟨ha₁, ha₂⟩⟩, ⟨b, ⟨hb₁, hb₂⟩⟩⟩ => ?_, by aesop⟩
  have : -(a + b) + b ∈ P := by exact add_mem (hsupp (show f (a + b) = 0 by simp_all)).2 hb₁
  aesop

@[simp]
theorem map_supportAddSubgroup {f : A →+* B} {P : RingPreordering A} {hf : Function.Surjective f}
    {hsupp : (RingHom.ker f : Set A) ⊆ supportAddSubgroup P} :
    supportAddSubgroup (map hf hsupp) = (supportAddSubgroup P).map f := by ext; simp

instance {f : A →+* B} {P : RingPreordering A} [HasIdealSupport P] (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ supportAddSubgroup P) :
    HasIdealSupport <| map hf hsupp where
  smul_mem_support x a ha := by
    rw [mem_map_supportAddSubgroup] at ha
    rcases ha with ⟨a', ha', rfl⟩
    rcases hf x with ⟨x', rfl⟩
    have := smul_mem_support P x' ha'
    aesop

@[simp↓]
theorem mem_map_support {f : A →+* B} {P : RingPreordering A} [HasIdealSupport P]
    {hf : Function.Surjective f}
    {hsupp : RingHom.ker f ≤ support P} {x : B} :
    x ∈ support (map hf hsupp) ↔ ∃ y ∈ support P, f y = x := by simp [support]

theorem _root_.Ideal.coe_map_of_surjective {R S F : Type*} [Semiring R] [Semiring S] [FunLike F R S]
    [RingHomClass F R S] {f : F} (hf : Function.Surjective f) {I : Ideal R} :
    Ideal.map f I = f '' I := by
  ext y
  exact Ideal.mem_map_iff_of_surjective _ hf

@[simp]
theorem map_support {f : A →+* B} {P : RingPreordering A} [HasIdealSupport P]
    {hf : Function.Surjective f} {hsupp : RingHom.ker f ≤ support P} :
    support (map hf hsupp) = (support P).map f := by
  ext; simp [Ideal.mem_map_iff_of_surjective f hf]

/-- The image of a prime ordering `P` along a surjective ring homomorphism
  with kernel contained in the support of `P` is a prime ordering. -/
instance {f : A →+* B} {P : RingPreordering A} [IsOrdering P] (hf : Function.Surjective f)
    (hsupp : RingHom.ker f ≤ support P) : IsOrdering <| map hf hsupp :=
  have : (support (map hf hsupp)).IsPrime := by
    simpa using Ideal.map_isPrime_of_surjective hf hsupp
  inferInstance

end RingPreordering
