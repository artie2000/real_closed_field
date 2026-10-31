import RealClosedField.Upstream
import Mathlib.Algebra.Order.Ring.Ordering.Basic

namespace Subsemiring

-- begin #45456

section CommRing

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
        {P : Subsemiring R} {P' : Subsemiring S}

namespace IsPreordering

@[gcongr]
theorem mono (hP : P.IsPreordering) {Q : Subsemiring R} (hPQ : P ≤ Q) (hQ : -1 ∉ Q) :
    Q.IsPreordering where

end IsPreordering

theorem IsPreordering.of_sumSq_le_of_isPointed [Nontrivial R]
    (h : .sumSq R ≤ P) (hP : P.IsPointed) : P.IsPreordering :=
  .of_sumSq_le h <| by grind [membership, isPointed_def, one_ne_zero]

theorem IsPreordering.of_isSpanning_of_isPointed [Nontrivial R]
    (hP₁ : P.IsSpanning) (hP₂ : P.IsPointed) : P.IsPreordering :=
  .of_sumSq_le_of_isPointed hP₁.sumSq_le hP₂

theorem IsOrdering.of_isSpanning_of_isPointed [IsDomain R]
    (hP₁ : P.IsSpanning) (hP₂ : P.IsPointed) : P.IsOrdering where
  isSpanning := hP₁
  support_ne_top := by simp [hP₂]
  mem_support_or_mem_support := by simp [hP₂]

-- end #45456

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
    have := AddSubmonoid.support_map (f := f.toAddMonoidHom) (M := P.toAddSubmonoid) hsupp
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

end Subsemiring

namespace Field

variable {F : Type*} [Field F]

variable (F) in
open Classical in
/-- Equivalence between orderings on a field `F` and linearly ordered field structures on `F`. -/
noncomputable def isOrderingLinearOrderEquiv :
    Equiv {O : Subsemiring F // O.IsOrdering}
          {_o : LinearOrder F // IsStrictOrderedRing F} where
  toFun := fun ⟨O, hO⟩ ↦
    let ⟨o, ho⟩ := Ring.isPointedLinearOrderEquiv F
      ⟨O, hO.isPreordering.isPointed, hO.isSpanning⟩
    ⟨o, IsOrderedRing.toIsStrictOrderedRing F⟩
  invFun := fun ⟨o, ho⟩ ↦
    let ⟨O, hO⟩ := (Ring.isPointedLinearOrderEquiv F).symm ⟨o, inferInstance⟩
    ⟨O, Subsemiring.IsOrdering.of_isSpanning_of_isPointed hO.2 hO.1⟩
  left_inv := fun ⟨_, _⟩ ↦ by ext; simp
  right_inv := fun ⟨_, _⟩ ↦ by
    -- TODO : fix proj-reduction with classes, simp, extends-projection
    ext : 1
    simp
    ext
    simp

@[simp]
theorem isOrderingLinearOrderEquiv_apply (O : Subsemiring F) (h : O.IsOrdering) :
    (isOrderingLinearOrderEquiv F ⟨O, h⟩ : LinearOrder F) =
    Ring.isPointedLinearOrderEquiv F ⟨O, h.isPreordering.isPointed, h.isSpanning⟩ := by
  simp [isOrderingLinearOrderEquiv]

@[simp]
theorem isOrderingLinearOrderEquiv_symm_apply_val
    (o : LinearOrder F) (h : IsStrictOrderedRing F) :
    ((isOrderingLinearOrderEquiv F).symm ⟨o, h⟩ : Subsemiring F) =
    (Ring.isPointedLinearOrderEquiv F).symm ⟨o, inferInstance⟩ := by
  simp [isOrderingLinearOrderEquiv]

end Field

-- TODO : `Ring.isOrderingLinearOrderEquiv` from unfinished part of `Algebra.Order.Cone.Order`
