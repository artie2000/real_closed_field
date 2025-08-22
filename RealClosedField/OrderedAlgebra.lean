/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib
import RealClosedField.Algebra.Order.Ring.Ordering.Adjoin
import RealClosedField.Algebra.Order.Ring.Ordering.Order

/- An ordered R-algebra is an R-algebra whose algebra map is order-preserving. -/
class IsOrderedAlgebra (R A : Type*) [CommSemiring R] [Semiring A] [LinearOrder R] [LinearOrder A]
    [IsOrderedRing R] [IsOrderedRing A] [Algebra R A] : Prop where
  monotone : Monotone <| algebraMap R A

attribute [mono] IsOrderedAlgebra.monotone

namespace IsOrderedAlgebra
open scoped algebraMap

variable {R A : Type*} [CommSemiring R] [Semiring A] [LinearOrder R] [LinearOrder A]
    [IsOrderedRing R] [IsOrderedRing A] [Algebra R A] [IsOrderedAlgebra R A]

theorem coe_mono {a b : R} (hab : a ≤ b) : (a : A) ≤ (b : A) := IsOrderedAlgebra.monotone hab

end IsOrderedAlgebra

variable {F K : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [Field K] [Algebra F K]

/- TODO : generalise to extensions of ordered rings -/

open Classical in
open scoped algebraMap in
noncomputable def RingOrdering_IsOrderedAlgebra_equiv_field :
    Equiv {O : RingPreordering K // O.IsOrdering ∧
            Subsemiring.map (algebraMap F K) (Subsemiring.nonneg F) ≤ O.toSubsemiring}
          {l : LinearOrder K // ∃ _ : IsStrictOrderedRing K, IsOrderedAlgebra F K} where
  toFun := fun ⟨O, hO, hO₂⟩ =>
    letI l := (RingOrdering_IsOrderedRing_equiv_field ⟨O, hO⟩).1
    letI hl := (RingOrdering_IsOrderedRing_equiv_field ⟨O, hO⟩).2
    ⟨l, ⟨inferInstance, ⟨by
      rw [monotone_iff_map_nonneg]
      intro a ha
      apply_fun (fun s ↦ s.carrier : Subsemiring K → Set K) at hO₂
      · simp only [Subsemiring.map_toSubmonoid, Subsemiring.coe_nonneg,
          Subsemiring.coe_carrier_toSubmonoid, RingPreordering.coe_toSubsemiring, Set.le_eq_subset,
          Set.image_subset_iff] at hO₂
        simpa [l] using hO₂ ha
      · exact fun _ _ h ↦ h⟩⟩⟩
  invFun := fun ⟨l, hl⟩ =>
    let O := RingOrdering_IsOrderedRing_equiv_field.symm ⟨l, hl.fst⟩
    ⟨O, O.property, fun x hx => by
    rcases hl with ⟨hl, hl₂⟩
    have : ∀ b : F, 0 ≤ b → 0 ≤ (b : K) := fun _ h ↦ by
      simpa using IsOrderedAlgebra.coe_mono (A := K) h
    aesop⟩
  left_inv := fun ⟨_, _, _⟩ => by ext; simp
  right_inv := fun _ => by ext; simp

@[simp]
theorem RingOrdering_IsOrderedAlgebra_equiv_field_apply_coe
    {O : RingPreordering K} (hO : O.IsOrdering)
    (hO₂ : Subsemiring.map (algebraMap F K) (Subsemiring.nonneg F) ≤ O.toSubsemiring) :
    (RingOrdering_IsOrderedAlgebra_equiv_field ⟨O, hO, hO₂⟩ : LinearOrder K) =
    RingOrdering_IsOrderedRing_equiv_field ⟨O, hO⟩ := rfl

@[simp]
theorem RingOrdering_IsOrderedAlgebra_equiv_field_symm_apply_coe
    (l : LinearOrder K) (hl : IsStrictOrderedRing K) (hl₂ : IsOrderedAlgebra F K) :
    (RingOrdering_IsOrderedAlgebra_equiv_field.symm ⟨l, hl, hl₂⟩ : RingPreordering K) =
    RingOrdering_IsOrderedRing_equiv_field.symm ⟨l, hl⟩ := rfl

open Classical Subsemiring in
theorem Field.exists_isOrderedAlgebra_iff_neg_one_notMem_sup :
    (∃ l : LinearOrder K, ∃ _ : IsStrictOrderedRing K, IsOrderedAlgebra F K) ↔
    -1 ∉ ((Subsemiring.nonneg F).map (algebraMap F K) ⊔ Subsemiring.sumSq K) := by
  rw [Equiv.exists_subtype_congr RingOrdering_IsOrderedAlgebra_equiv_field.symm]
  refine ⟨fun ⟨O, hO, hO₂⟩ hc => ?_, fun h => ?_⟩
  · suffices Subsemiring.map (algebraMap F K) (Subsemiring.nonneg F) ⊔ Subsemiring.sumSq K ≤
             O.toSubsemiring from
      RingPreordering.neg_one_notMem _ <| this hc
    rw [sup_le_iff]
    exact ⟨hO₂, fun _ => by aesop⟩
  · rcases RingPreordering.exists_le_isOrdering <| .mkOfSubsemiring
        ((Subsemiring.nonneg F).map (algebraMap F K) ⊔ Subsemiring.sumSq K) (by simp) h with
      ⟨O, hO, hO₂⟩
    refine ⟨O, ⟨inferInstance, ?_⟩⟩
    intro _ hx
    simpa using hO <| le_sup_left (α := Subsemiring K) hx

open scoped Pointwise in
theorem sup_map_nonneg_sumSq_eq_addSubmonoid_closure_set_mul :
    ↑((Subsemiring.nonneg F).map (algebraMap F K) ⊔ Subsemiring.sumSq K) =
    (Submodule.span (Subsemiring.nonneg F) {x : K | IsSquare x} : Set K) := by
  rw [← Subsemiring.closure_isSquare, ← Subsemiring.closure_eq <| Subsemiring.map ..,
      ← Subsemiring.closure_union, ← Subsemiring.closure_submonoid_closure,
      ← Submonoid.subsemiringClosure_eq_closure, Submonoid.subsemiringClosure_coe,
      ← Submodule.coe_toAddSubmonoid, Submodule.span_eq_closure]
  congr
  rw [← Subsemiring.coe_toSubmonoid, ← Submonoid.coe_square, ← Submonoid.sup_eq_closure,
      Submonoid.coe_sup, Subsemiring.coe_toSubmonoid]
  ext x
  simp [Set.mem_mul, Set.mem_smul, Subsemiring.smul_def, ← Algebra.smul_def]

open scoped Pointwise in
theorem Field.exists_isOrderedAlgebra_iff_neg_one_notMem_closure_mul :
    (∃ l : LinearOrder K, ∃ _ : IsStrictOrderedRing K, IsOrderedAlgebra F K) ↔
    -1 ∉ Submodule.span (Subsemiring.nonneg F) {x : K | IsSquare x} := by
  rw [← SetLike.mem_coe, ← sup_map_nonneg_sumSq_eq_addSubmonoid_closure_set_mul, SetLike.mem_coe,
    Field.exists_isOrderedAlgebra_iff_neg_one_notMem_sup]

open scoped Pointwise algebraMap in
theorem Field.exists_isOrderedAlgebra_of_projection
    (π : K →ₗ[F] F) (hπ : ∀ x, x ≠ 0 → 0 < π (x * x)) :
    (∃ l : LinearOrder K, ∃ _ : IsStrictOrderedRing K, IsOrderedAlgebra F K) := by
  rw [Field.exists_isOrderedAlgebra_iff_neg_one_notMem_closure_mul]
  have ih : ∀ x ∈ Submodule.span (Subsemiring.nonneg F) {x : K | IsSquare x}, 0 ≤ π x := by
    apply Submodule.closure_induction
    · simp
    · intro x y _ _ _ _
      linarith [map_add π x y]
    · rintro ⟨r, hr⟩ x ⟨d, rfl⟩
      by_cases hd : d = 0
      · simp [hd]
      · simpa using (mul_nonneg_iff_of_pos_right (hπ d hd)).mpr hr
  intro h
  simpa using not_le_of_gt (hπ 1 (by simp)) (by simpa using ih _ h)

open Polynomial in
theorem X_sq_sub_C_irreducible_iff_not_isSquare {F : Type*} [Field F] (a : F) :
    Irreducible (X ^ 2 - C a) ↔ ¬ IsSquare a := by
  rw [isSquare_iff_exists_sq]
  have := X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two (a := a)
  simp [eq_comm (a := a), this]

open Polynomial in
theorem adj_sqrt_ordered {a : F} (ha : 0 ≤ a) (ha₂ : ¬ IsSquare a) :
    letI K := AdjoinRoot (X ^ 2 - C a)
    (∃ l : LinearOrder K, ∃ _ : IsStrictOrderedRing K, IsOrderedAlgebra F K) := by
  have : 0 < a := lt_of_le_of_ne ha (by aesop)
  rw [← X_sq_sub_C_irreducible_iff_not_isSquare] at ha₂
  have := Fact.mk ha₂
  set B := AdjoinRoot.powerBasis <| show X ^ 2 - C a ≠ 0 by apply_fun natDegree; simp
  have Bdim : B.dim = 2 := by simp [B]
  have Bgen : B.gen = AdjoinRoot.root (X ^ 2 - C a) := by simp [B]
  rcases B with ⟨α, n, B, hB⟩
  simp only at Bdim Bgen
  revert B
  rw [Bdim, Bgen]
  intro B hB
  refine Field.exists_isOrderedAlgebra_of_projection (Module.Basis.coord B 0) fun x hx => ?_
  rw [← Module.Basis.sum_repr B x]
  simp [hB, Algebra.smul_def, -AdjoinRoot.algebraMap_eq]
  ring_nf
  have : AdjoinRoot.root (X ^ 2 - C a) ^ 2 - algebraMap F _ a = 0 := by
      have := AdjoinRoot.eval₂_root (X ^ 2 - C a)
      simp_all
  rw [show AdjoinRoot.root (X ^ 2 - C a) ^ 2 = algebraMap F _ a by linear_combination this]
  simp [-AdjoinRoot.algebraMap_eq, Algebra.algebraMap_eq_smul_one, pow_two]
  rw [show _ * 2 = (2 : F) • AdjoinRoot.root (X ^ 2 - C a) by rw [mul_comm]; norm_cast; simp,
      map_smul,
      show 1 = B 0 by simp [hB],
      show AdjoinRoot.root (X ^ 2 - C a) = B 1 by simp [hB]]
  simp [← pow_two]
  suffices h : B.repr x 0 ≠ 0 ∨ B.repr x 1 ≠ 0 by
    cases h with
    | inl h => linear_combination pow_two_pos_of_ne_zero h + a * (sq_nonneg <| B.repr x 1)
    | inr h => linear_combination (sq_nonneg <| B.repr x 0) + a * (pow_two_pos_of_ne_zero h)
  by_contra h
  exact hx <| (Module.Basis.forall_coord_eq_zero_iff B).mp <| fun i => by fin_cases i <;> simp_all

open scoped Polynomial in
theorem Polynomial.exists_odd_natDegree_monic_irreducible_factor {F : Type*} [Field F] (f : F[X])
    (hf : Odd f.natDegree) : ∃ g : F[X], (Odd g.natDegree) ∧ g.Monic ∧ Irreducible g ∧ g ∣ f := by
  induction h : f.natDegree using Nat.strong_induction_on generalizing f with | h n ih =>
    have hu : ¬IsUnit f := Polynomial.not_isUnit_of_natDegree_pos _ (Odd.pos hf)
    rcases Polynomial.exists_monic_irreducible_factor f hu with ⟨g, g_monic, g_irred, g_div⟩
    by_cases g_deg : Odd g.natDegree
    · exact ⟨g, g_deg, g_monic, g_irred, g_div⟩
    · rcases g_div with ⟨k, hk⟩
      have : f.natDegree = g.natDegree + k.natDegree := by
        simpa [hk] using Polynomial.natDegree_mul (g_irred.ne_zero) (fun _ ↦ by simp_all)
      have := Irreducible.natDegree_pos g_irred
      rcases ih k.natDegree (by omega) k (by grind) rfl with ⟨l, h₁, h₂, h₃, h₄⟩
      exact ⟨l, h₁, h₂, h₃, dvd_trans h₄ (dvd_iff_exists_eq_mul_left.mpr ⟨g, hk⟩)⟩

variable  {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜] [AddCommMonoid E] [Module 𝕜 E]
#synth Module (Subsemiring.nonneg 𝕜) E

open scoped Polynomial in
theorem lift_poly_span_nonneg_isSquare {f : F[X]} (hAdj : IsAdjoinRootMonic K f) {x : K}
    (hx : x ∈ Submodule.span (Subsemiring.nonneg F) ({x : K | IsSquare x})) :
    ∃ g, hAdj.map g = x ∧
      g ∈ Submodule.span (Subsemiring.nonneg F)
            ((fun x ↦ x * x) '' {g : F[X] | g.natDegree < f.natDegree}) := by
  have f_ne_one : f ≠ 1 := fun hc ↦ by aesop (add safe forward hAdj.deg_ne_zero)
  induction hx using Submodule.span_induction with
  | zero => exact ⟨0, by simp⟩
  | mem x hx =>
      rcases hx with ⟨y, rfl⟩
      refine ⟨hAdj.modByMonicHom y * hAdj.modByMonicHom y, by simp, Submodule.mem_span_of_mem ?_⟩
      exact ⟨hAdj.modByMonicHom y,
          by simpa using Polynomial.natDegree_modByMonic_lt _ hAdj.monic f_ne_one⟩
  | smul r x hx ih =>
      rcases ih with ⟨g, rfl, hg⟩
      exact ⟨r • g, by simp? [Subsemiring.smul_def], by aesop⟩
  | add _ _ _ _ ihx ihy =>
      rcases ihx with ⟨g₁, rfl, hg₁⟩
      rcases ihy with ⟨g₂, rfl, hg₂⟩
      exact ⟨g₁ + g₂, by aesop⟩

open scoped Polynomial in
theorem minus_one_notMem_span_nonneg_isSquare_mod_f {f : F[X]}
    (hf₁ : f.Monic) (hf₂ : Irreducible f) (hf₃ : Odd f.natDegree) {g : F[X]}
    (hg : g ∈ Submodule.span (Subsemiring.nonneg F)
                ((fun x ↦ x * x) '' {g : F[X] | g.natDegree < f.natDegree})) :
    ¬(f ∣ g + 1) := by
  have g_facts :
    ∀ f : F [X], f.natDegree > 0 →
                 ∀ g ∈ Submodule.span (Subsemiring.nonneg F)
                         ((fun x ↦ x * x) '' {g : F[X] | g.natDegree < f.natDegree}),
      0 ≤ g.leadingCoeff ∧ Even g.natDegree ∧ g.natDegree < 2 * f.natDegree := fun f hf h hg ↦ by
    induction hg using Submodule.span_induction with
    | zero => simp [hf]
    | mem g hg =>
        rcases hg with ⟨r, _, rfl⟩
        by_cases hz : r = 0
        · simp_all
        · simp_all only [Polynomial.natDegree_mul hz hz, Even.add_self, true_and, Set.mem_setOf_eq,
                        Polynomial.leadingCoeff_mul]
          exact ⟨mul_self_nonneg _, by linarith⟩
    | smul x g _ ihg =>
        rcases x with ⟨x, hx⟩
        rw [Subsemiring.smul_def]
        by_cases hz : x = 0
        · simp [hf, hz]
        · exact ⟨by simpa [Polynomial.smul_eq_C_mul] using mul_nonneg hx ihg.1,
                by simpa [Polynomial.natDegree_smul _ hz] using ihg.2⟩
    | add g h _ _ ihg ihh =>
        by_cases hdeg : g.degree = h.degree
        · by_cases hz : g + h = 0
          · simp [hf, hz]
          · have hz' : h ≠ 0 := fun hc ↦ by simp_all
            have hlc : g.leadingCoeff + h.leadingCoeff ≠ 0 := fun hc ↦ by
              simp_all [add_eq_zero_iff_of_nonneg ihg.1 ihh.1]
            have : (g + h).degree = _ := Polynomial.degree_add_eq_of_leadingCoeff_add_ne_zero hlc
            simp_all only [Polynomial.leadingCoeff_add_of_degree_eq hdeg hlc,
                          Polynomial.degree_eq_natDegree hz', Polynomial.degree_eq_natDegree hz,
                          max_self, Nat.cast_inj, and_true]
            exact add_nonneg ihg.1 ihh.1
        · cases lt_or_gt_of_ne hdeg with
          | inl hdeg => simpa [Polynomial.leadingCoeff_add_of_degree_lt hdeg,
                               Polynomial.natDegree_add_eq_right_of_degree_lt hdeg] using ihh
          | inr hdeg => simpa [Polynomial.leadingCoeff_add_of_degree_lt' hdeg,
                               Polynomial.natDegree_add_eq_left_of_degree_lt hdeg] using ihg
  induction h : f.natDegree using Nat.strong_induction_on generalizing f g with | h n ih =>
    rcases g_facts _ (Irreducible.natDegree_pos hf₂) _ hg with
      ⟨leadingCoeff_nonneg, natDegree_even, natDegree_lt⟩
    have : f ≠ 0 := Irreducible.ne_zero hf₂
    intro hdiv
    have : g + 1 ≠ 0 := fun hc ↦ by
      simp [show g = -1 by linear_combination hc] at leadingCoeff_nonneg
      linarith
    rcases hdiv with ⟨k, hk⟩
    have : k ≠ 0 := fun _ ↦ by simp_all
    have : g.natDegree = f.natDegree + k.natDegree := by
      rw [← Polynomial.natDegree_mul ‹f ≠ 0› ‹k ≠ 0›, ← hk, ← Polynomial.C_1,
          Polynomial.natDegree_add_C]
    rcases Polynomial.exists_odd_natDegree_monic_irreducible_factor k (by grind) with
      ⟨k', k'_deg, k'_Monic, k'_irred, k'_dvd⟩
    have : Fact (Irreducible k') := Fact.mk k'_irred
    have : (AdjoinRoot.mk k') g ∈ Submodule.span (Subsemiring.nonneg F) {x | IsSquare x} := by
      let mkₐ := (AdjoinRoot.mkₐ k').toLinearMap.restrictScalars (Subsemiring.nonneg F)
      have : ⇑mkₐ '' ((fun x ↦ x * x) '' {g | g.natDegree < f.natDegree}) ⊆ {x | IsSquare x} :=
        fun x hx ↦ by
          simp only [Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and] at hx
          rcases hx with ⟨r, hr, rfl⟩
          simp [mkₐ]
      have := Submodule.span_mono (R := Subsemiring.nonneg F) this
      rw [← Submodule.map_span] at this
      exact Set.mem_of_subset_of_mem this ⟨g, hg, rfl⟩
    rcases lift_poly_span_nonneg_isSquare (AdjoinRoot.isAdjoinRootMonic _ k'_Monic) this with
      ⟨g', hg'_map, hg'_mem⟩
    exact ih k'.natDegree (by linarith [Polynomial.natDegree_le_of_dvd k'_dvd ‹k ≠ 0›])
      ‹_› ‹_› ‹_› hg'_mem rfl <|
      (dvd_iff_dvd_of_dvd_sub <| by simpa [AdjoinRoot.isAdjoinRoot_map_eq_mkₐ] using hg'_map).mpr <|
        dvd_trans k'_dvd <| dvd_iff_exists_eq_mul_left.mpr ⟨f, hk⟩

open scoped Pointwise in
theorem odd_deg_ordered (h_rank : Odd <| Module.finrank F K) :
    (∃ l : LinearOrder K, ∃ _ : IsStrictOrderedRing K, IsOrderedAlgebra F K) := by
  rw [Field.exists_isOrderedAlgebra_iff_neg_one_notMem_closure_mul]
  have : FiniteDimensional F K := Module.finite_of_finrank_pos <| Odd.pos h_rank
  rcases Field.exists_primitive_element F K with ⟨α, hα⟩
  have int := IsIntegral.of_finite F α
  have hAdj := IsAdjoinRootMonic.mkOfPrimitiveElement int hα
  intro hc
  rcases lift_poly_span_nonneg_isSquare hAdj (x := -1) hc with ⟨g, hg_map, hg_mem⟩
  apply minus_one_notMem_span_nonneg_isSquare_mod_f hAdj.monic (minpoly.irreducible int)
          (by simpa [← hAdj.finrank] using h_rank) hg_mem
  rw [← hAdj.map_eq_zero_iff]
  simp [hg_map]

#min_imports
