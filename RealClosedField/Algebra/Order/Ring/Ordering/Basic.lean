import RealClosedField.Algebra.Order.Ring.Ordering.Defs
import Mathlib.Algebra.Order.Ring.Ordering.Basic
import Mathlib.Tactic.Field
import Mathlib.Tactic.LinearCombination

namespace Subsemiring

section CommRing

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
        {P : Subsemiring R} (P' : Subsemiring S)

namespace IsPreordering

theorem of_le (hP : P.IsPreordering) {Q : Subsemiring R} (hPQ : P ≤ Q) (hQ : -1 ∉ Q) :
    Q.IsPreordering where
  mem_of_isSquare := by grind [IsConcreteLE.le_iff, IsPreordering.mem_of_isSquare]

-- TODO : membership tag
theorem unitsInv_mem (hP : P.IsPreordering) {a : Rˣ} (ha : ↑a ∈ P) : ↑a⁻¹ ∈ P := by
  simpa using show (a * (a⁻¹ * a⁻¹) : R) ∈ P by grind [mul_mem, IsPreordering.mul_self_mem]

theorem one_notMem_support (hP : P.IsPreordering) : 1 ∉ P.support := fun h ↦
  P.neg_one_notMem hP h.2

theorem support_ne_top (hP : P.IsPreordering) : P.support ≠ ⊤ := fun h ↦
  one_notMem_support hP (by simp [h])

theorem isOrdering_iff (hP : P.IsPreordering) :
    P.IsOrdering ↔ ∀ a b : R, -(a * b) ∈ P → a ∈ P ∨ b ∈ P where
  mp hP a b _ := by
    by_contra
    have : a * b ∈ P := by
      have := Subsemiring.isSpanning_def.mp hP.isSpanning
      grind [mul_mem, mul_neg, neg_mul, neg_neg]
    have : a ∈ P.support ∨ b ∈ P.support :=
      Ideal.IsPrime.mem_or_mem hP.isPrime_supportIdeal (by simp; grind)
    grind [Subsemiring.mem_support]
  mpr h := by
    refine ⟨?_, hP.support_ne_top, fun {x y} ↦ ?_⟩
    · simp [AddSubmonoid.IsSpanning]
      grind [hP.mul_self_mem, neg_mul, mul_neg, neg_neg] -- TODO : figure out why `grind` doesn't know `neg_neg`
    · simp_rw [Subsemiring.mem_support]
      by_contra
      have := h (-x) y
      have := h (-x) (-y)
      have := h x y
      have := h x (-y)
      cases (by simp_all : x ∈ P ∨ -x ∈ P) <;> simp_all

theorem smul_mem_support_of_isUnit_two (hP : P.IsPreordering) (h : IsUnit (2 : R))
    (x : R) {a : R} (ha : a ∈ P.support) : x * a ∈ P.support := by
  rcases h.exists_right_inv with ⟨half, h2⟩
  rw [Subsemiring.mem_support] at *
  rw [show x = ((1 + x) * half) ^ 2 - ((1 - x) * half) ^ 2 by
    linear_combination (- x - x * half * 2) * h2]
  grind [sub_eq_add_neg, add_mem, mul_mem, mul_neg_mem, IsPreordering.pow_two_mem, neg_add_rev,
    neg_neg, sub_eq_add_neg, sub_mul]

end IsPreordering

theorem IsPreordering.of_isSpanning_of_isPointed [Nontrivial R]
    (hP₁ : P.IsSpanning) (hP₂ : P.IsPointed) : P.IsPreordering :=
  .of_ne_top hP₁ fun hc ↦ one_ne_zero' R (by simp_all [AddSubmonoid.IsPointed]) -- TODO : ¬ T.IsPointed

theorem IsPreordering.of_isPointed [Nontrivial R]
    (hP : P.IsPointed) (h : .sumSq R ≤ P) : P.IsPreordering where
  mem_of_isSquare hx := h (by simpa using hx.isSumSq)
  neg_one_notMem := by
    rw [Subsemiring.isPointed_def] at hP
    grind [one_mem, one_ne_zero]

theorem IsOrdering.of_isSpanning_of_isPointed [IsDomain R]
    (hP₁ : P.IsSpanning) (hP₂ : P.IsPointed) : P.IsOrdering where
  isSpanning := hP₁
  support_ne_top := by simp [hP₂]
  mem_support_or_mem_support := by simp [hP₂]

-- PR SPLIT ↑1 ↓2

-- TODO : upstream and add similar
attribute [simp] Submonoid.mem_sInf
attribute [simp] AddSubmonoid.mem_sInf
attribute [simp] Subsemiring.mem_sInf

theorem IsPreordering.inf {P₁ P₂ : Subsemiring R} (hP₁ : P₁.IsPreordering) (hP₂ : P₂.IsPreordering) :
    (P₁ ⊓ P₂).IsPreordering where
  mem_of_isSquare := by grind [mem_inf, mem_of_isSquare]
  neg_one_notMem := by grind [mem_inf, neg_one_notMem]

theorem IsPreordering.sInf {S : Set (Subsemiring R)}
    (hSn : S.Nonempty) (hS : ∀ s ∈ S, s.IsPreordering) : (sInf S).IsPreordering where
  mem_of_isSquare := by grind [mem_sInf, mem_of_isSquare]
  neg_one_notMem := by
    simpa using ⟨_, hSn.some_mem, (hS _ hSn.some_mem).neg_one_notMem⟩

theorem IsPreordering.sSup  {S : Set (Subsemiring R)}
    (hSn : S.Nonempty) (hSd : DirectedOn (· ≤ ·) S)
    (hS : ∀ s ∈ S, s.IsPreordering) : (sSup S).IsPreordering where
  mem_of_isSquare x := by
    have := Set.Nonempty.some_mem hSn
    simpa [mem_sSup_of_directedOn hSn hSd] using ⟨_, this, by aesop⟩
  neg_one_notMem := by
    simpa [mem_sSup_of_directedOn hSn hSd] using (fun _ hx ↦ (hS _ hx).neg_one_notMem)

theorem IsOrdering.comap (hP' : P'.IsOrdering) : IsOrdering (P'.comap f) :=
  have := hP'.isPrime_supportIdeal
  .of_isPrime_supportIdeal (isSpanning_comap f hP'.isSpanning) <| by
    convert (P'.supportIdeal hP'.isSpanning).comap_isPrime f
    simp [← Submodule.toAddSubgroup_inj, Ideal.comap_eq_submodule_comap]

theorem IsPreordering.comap (hP' : P'.IsPreordering) : (P'.comap f).IsPreordering where
  mem_of_isSquare := by grind [mem_comap, mem_of_isSquare, IsSquare.map]
  neg_one_notMem := by grind [mem_comap, neg_one_notMem]

variable {f} in
theorem IsOrdering.map (hP : P.IsOrdering) (hf : Function.Surjective f)
    (hsupp : RingHom.ker f ≤ P.supportIdeal hP.isSpanning) : IsOrdering (P.map f) :=
  have := hP.isPrime_supportIdeal
  have : RingHomSurjective f := ⟨hf⟩
  .of_isPrime_supportIdeal (isSpanning_map hP.isSpanning hf) <| by
    convert Ideal.map_isPrime_of_surjective hf hsupp
    -- TODO : fix defeq abuse at `hsupp` and remove hints
    have := AddSubmonoid.map_support (f := f.toAddMonoidHom) (M := P.toAddSubmonoid) hsupp
    -- TODO : fix coercion hell for `map` (by fixing defs) and change to `simp` proof
    simp_rw [← Submodule.toAddSubgroup_inj, Ideal.map_eq_submodule_map, Submodule.map_toAddSubgroup',
      supportIdeal_toAddSubgroup, map_toAddSubmonoid, this, RingHom.toAddMonoidHom_toSemilinearMap]

variable {f} in
theorem IsPreordering.map (hP : P.IsPreordering) (hf : Function.Surjective f)
    (hsupp : f.toAddMonoidHom.ker ≤ P.toAddSubmonoid.support) : (P.map f).IsPreordering where
  mem_of_isSquare hx := by
    rcases isSquare_subset_image_isSquare hf hx with ⟨x', ⟨_, _⟩, _⟩
    exact ⟨x', by simp_all⟩
  neg_one_notMem := fun ⟨x', hx', _⟩ ↦ by
    have : -(1 + x') + x' ∈ P := add_mem (hsupp (by simp [*])).2 hx'
    simp [hP.neg_one_notMem] at this

end CommRing

-- PR SPLIT ↑2 ↓1

section Field

variable {F : Type*} [Field F] {P : Subsemiring F}

namespace IsPreordering

-- TODO : membership
theorem inv_mem (hP : IsPreordering P) {a : F} (ha : a ∈ P) : a⁻¹ ∈ P := by
  suffices a * (a⁻¹ * a⁻¹) ∈ P by convert this; field
  grind [mul_mem, IsPreordering.mul_self_mem]

theorem isPointed (hP : IsPreordering P) : P.IsPointed := by
  rw [Subsemiring.isPointed_def]
  grind [P.neg_one_notMem hP, neg_mul_mem, inv_mem]

end IsPreordering

end Field

end Subsemiring
