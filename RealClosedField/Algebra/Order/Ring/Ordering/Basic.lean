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

@[aesop unsafe 90% apply (rule_sets := [SetLike])]
theorem inv_mem {a : Rˣ} (ha : ↑a ∈ P) : ↑a⁻¹ ∈ P := by
  have : (a * (a⁻¹ * a⁻¹) : R) ∈ P := by aesop (config := { enableSimp := false })
  simp_all

@[aesop unsafe 90% apply (rule_sets := [SetLike])]
theorem Field.inv_mem {F : Type*} [Field F] {P : RingPreordering F} {a : F} (ha : a ∈ P) :
    a⁻¹ ∈ P := by
  have mem : a * (a⁻¹ * a⁻¹) ∈ P := by aesop
  field_simp at mem
  simp_all

@[aesop unsafe 80% apply (rule_sets := [SetLike])]
theorem mem_of_isSumSq {x : R} (hx : IsSumSq x) : x ∈ P := by
  induction hx using IsSumSq.rec' <;> aesop

section mkOfSubsemiring

variable {R : Type*} [CommRing R] {P : Subsemiring R}
  {le : Subsemiring.sumSq R ≤ P} {minus : -1 ∉ P}

variable (P le minus) in
/- Construct a preordering from a subsemiring. -/
def mkOfSubsemiring : RingPreordering R where toSubsemiring := P

@[simp]
theorem mkOfSubsemiring_toSubsemiring : (mkOfSubsemiring P le minus).toSubsemiring = P := rfl
@[simp] theorem mem_mkOfSubsemiring {x : R} : x ∈ mkOfSubsemiring P le minus ↔ x ∈ P := .rfl
@[simp] theorem coe_mkOfSubsemiring : mkOfSubsemiring P le minus = (P : Set R) := rfl

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
  zero_mem' := by simpa using sq 0
  one_mem' := by simpa using sq 1

@[simp] theorem mem_mk' {x : R} : x ∈ mk' P add mul sq minus ↔ x ∈ P := .rfl
@[simp, norm_cast] theorem coe_mk' : mk' P add mul sq minus = P := rfl

end mk'

/-!
### Supports
-/

section neq_top

variable (P)

theorem one_notMem_supportAddSubgroup : 1 ∉ P.supportAddSubgroup :=
  fun h => RingPreordering.neg_one_notMem P (by simpa using h.2)

theorem one_notMem_support [P.HasIdealSupport] : 1 ∉ P.support := by
  simpa using one_notMem_supportAddSubgroup P

theorem supportAddSubgroup_ne_top : P.supportAddSubgroup ≠ ⊤ :=
  fun h => RingPreordering.neg_one_notMem P (by simp [h] : 1 ∈ P.supportAddSubgroup).2

theorem support_ne_top [P.HasIdealSupport] : P.support ≠ ⊤ := by
  apply_fun Submodule.toAddSubgroup
  simpa using supportAddSubgroup_ne_top P

/- Constructor for IsOrdering that doesn't require `ne_top'`. -/
def IsOrdering.mk' [HasMemOrNegMem P]
    (h : ∀ {x y}, x * y ∈ P.support → x ∈ P.support ∨ y ∈ P.support) : P.IsOrdering where
  ne_top' := support_ne_top P
  mem_or_mem' := h

end neq_top

namespace HasIdealSupport

theorem smul_mem [P.HasIdealSupport]
  (x : R) {a : R} (h₁a : a ∈ P) (h₂a : -a ∈ P) : x * a ∈ P := by
  rw [hasIdealSupport_iff] at ‹P.HasIdealSupport›
  simp [*]

theorem neg_smul_mem [P.HasIdealSupport]
  (x : R) {a : R} (h₁a : a ∈ P) (h₂a : -a ∈ P) : -(x * a) ∈ P := by
  rw [hasIdealSupport_iff] at ‹P.HasIdealSupport›
  simp [*]

end HasIdealSupport

theorem hasIdealSupport_of_isUnit_2 (isUnit_2 : IsUnit (2 : R)) : P.HasIdealSupport := by
  rw [hasIdealSupport_iff]
  intro x a _ _
  obtain ⟨half, h2⟩ := IsUnit.exists_left_inv isUnit_2
  set y := (1 + x) * half
  set z := (1 - x) * half
  have mem : (y * y) * a + (z * z) * -a ∈ P ∧ (y * y) * -a + (z * z) * a ∈ P := by aesop
  rw [show x = y * y - z * z by linear_combination (-(2 * x * half) - 1 * x) * h2]
  ring_nf at mem ⊢
  assumption

section Field

variable {F : Type*} [Field F] (P : RingPreordering F)

variable {P} in
@[aesop unsafe 70% apply]
protected theorem eq_zero_of_mem_of_neg_mem {x} (h : x ∈ P) (h2 : -x ∈ P) : x = 0 := by
  by_contra
  have mem : -x * x⁻¹ ∈ P := by aesop (erase simp neg_mul)
  field_simp at mem
  exact RingPreordering.neg_one_notMem P mem

theorem supportAddSubgroup_eq_bot : P.supportAddSubgroup = ⊥ := by
  ext; aesop (add simp mem_supportAddSubgroup)

instance : P.HasIdealSupport where
  smul_mem_support := by simp [supportAddSubgroup_eq_bot]

@[simp] theorem support_eq_bot : P.support = ⊥ := by
  apply_fun Submodule.toAddSubgroup using Submodule.toAddSubgroup_injective
  simpa using supportAddSubgroup_eq_bot P

instance : P.support.IsPrime := by simpa using Ideal.bot_prime

end Field

section HasMemOrNegMem

variable [HasMemOrNegMem P]

@[aesop unsafe 70% apply]
theorem neg_mem_of_notMem (x : R) (h : x ∉ P) : -x ∈ P := by
  have := mem_or_neg_mem P x
  simp_all

@[aesop unsafe 70% apply]
theorem mem_of_not_neg_mem (x : R) (h : -x ∉ P) : x ∈ P := by
  have := mem_or_neg_mem P x
  simp_all

end HasMemOrNegMem

theorem isOrdering_iff :
    P.IsOrdering ↔ (∀ a b : R, -(a * b) ∈ P → a ∈ P ∨ b ∈ P) := by
  refine ⟨fun prime a b h₁ => ?_, fun h => ?_⟩
  · by_contra
    have : a * b ∈ P := by simpa using mul_mem (by aesop : -a ∈ P) (by aesop : -b ∈ P)
    have : a ∈ P.support ∨ b ∈ P.support :=
      Ideal.IsPrime.mem_or_mem inferInstance (by simp_all [mem_support])
    simp_all [mem_support]
  · have : HasMemOrNegMem P := ⟨by aesop⟩
    refine IsOrdering.mk' P (fun {x y} hxy => ?_)
    by_contra
    cases (by aesop : x ∈ P ∨ -x ∈ P) with
    | inl =>  have := h (-x) y
              have := h (-x) (-y)
              simp_all [mem_support]
    | inr =>  have := h x y
              have := h x (-y)
              simp_all [mem_support]

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

@[simp]
theorem supportAddSubgroup_inf :
    (P₁ ⊓ P₂).supportAddSubgroup = P₁.supportAddSubgroup ⊓ P₂.supportAddSubgroup := by
  ext
  simp only [mem_supportAddSubgroup, mem_inf, AddSubgroup.mem_inf]
  tauto

instance [P₁.HasIdealSupport] [P₂.HasIdealSupport] : (P₁ ⊓ P₂).HasIdealSupport := sorry

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

/- TODO : support sInf -/

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

/- TODO : support sSup -/

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
  mem_of_isSquare' := by aesop (add unsafe apply IsSquare.map) /- TODO : remove add .. once change is merged -/
  neg_one_notMem' := by aesop

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
