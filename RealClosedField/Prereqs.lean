/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.Qify

/- Lemmas that should be upstreamed to Mathlib -/

@[aesop 70%]
theorem mem_sup_of_mem_left {R : Type*} [Semiring R] {a b : Subsemiring R} {x : R} :
    x ∈ a → x ∈ a ⊔ b := by gcongr; exact le_sup_left

@[aesop 70%]
theorem mem_sup_of_mem_right {R : Type*} [Semiring R] {a b : Subsemiring R} {x : R} :
    x ∈ b → x ∈ a ⊔ b := by gcongr; exact le_sup_right

theorem Ideal.irreducible_of_isMaximal_span_singleton {R : Type*} [CommRing R] [IsDomain R] {m : R}
    (hm : m ≠ 0) (hmax : (span {m}).IsMaximal) : Irreducible m :=
  ((span_singleton_prime hm).mp hmax.isPrime).irreducible

theorem Ideal.span_singleton_irreducible {R : Type*} [CommRing R] [IsPrincipalIdealRing R]
    [IsDomain R] {m : R} (hm : m ≠ 0) : (span {m}).IsMaximal ↔ Irreducible m where
  mp := irreducible_of_isMaximal_span_singleton hm
  mpr := PrincipalIdealRing.isMaximal_of_irreducible

theorem Ideal.Quotient.isField_of_irreducible {R : Type*} [CommRing R] [IsPrincipalIdealRing R]
    {m : R} (hirr : Irreducible m) : IsField (R ⧸ span {m}) :=
  (maximal_ideal_iff_isField_quotient _).mp (PrincipalIdealRing.isMaximal_of_irreducible hirr)

theorem Ideal.Quotient.irreducible_of_isField
    {R : Type*} [CommRing R] [IsDomain R] {m : R} (hm : m ≠ 0) (hf : IsField <| R ⧸ span {m}) :
    Irreducible m :=
  irreducible_of_isMaximal_span_singleton hm ((maximal_ideal_iff_isField_quotient _).mpr hf)

theorem Ideal.Quotient.irreducible_iff_isField
    {R : Type*} [CommRing R] [IsPrincipalIdealRing R] [IsDomain R] {m : R} (hm : m ≠ 0) :
    Irreducible m ↔ IsField (R ⧸ Ideal.span {m}) where
  mp := Ideal.Quotient.isField_of_irreducible
  mpr := Ideal.Quotient.irreducible_of_isField hm

theorem Polynomial.natDegree_eq_one_iff_degree_eq_one
    {R : Type*} [Semiring R] {p : Polynomial R} :
    p.degree = 1 ↔ p.natDegree = 1 :=
  degree_eq_iff_natDegree_eq_of_pos (Nat.zero_lt_one)

theorem Polynomial.natDegree_eq_iff_degree_eq_of_atLeastTwo
    {R : Type*} [Semiring R] {p : Polynomial R} {n : ℕ} [Nat.AtLeastTwo n] :
    p.degree = n ↔ p.natDegree = n :=
  degree_eq_iff_natDegree_eq_of_pos (Nat.pos_of_neZero n)

@[simp]
theorem Polynomial.natDegree_add_one {R : Type u} [Semiring R] {p : Polynomial R} :
    (p + 1).natDegree = p.natDegree := by
  simp [← C_1, -map_one]

@[simp]
theorem Polynomial.natDegree_one_add {R : Type u} [Semiring R] {p : Polynomial R} :
    (1 + p).natDegree = p.natDegree := by
  simp [← C_1, -map_one]

@[simp]
theorem Polynomial.natDegree_normalize {R : Type u} [Field R] {p : Polynomial R} [DecidableEq R] :
    (normalize p).natDegree = p.natDegree :=
  natDegree_eq_of_degree_eq degree_normalize

open Polynomial in
example {R : Type u} [CommRing R] (a b : R) :
    ((X - C a) ^ 2 + C b ^ 2) = (X ^ 2 + C b ^ 2).comp (X - C a) := by
  simp

@[simp]
theorem Polynomial.natDegree_X_sub_C_sq_add_C_sq
    {R : Type u} [CommRing R] [NoZeroDivisors R] [Nontrivial R] (a b : R) :
    ((X - C a) ^ 2 + C b ^ 2).natDegree = 2 := by
  rw [show ((X - C a) ^ 2 + C b ^ 2) = (X ^ 2 + C b ^ 2).comp (X - C a) by simp,
      Polynomial.natDegree_comp]
  simp [← map_pow]

@[simp]
theorem Polynomial.monic_X_sub_C_sq_add_C_sq
    {R : Type u} [CommRing R] [NoZeroDivisors R] [Nontrivial R] (a b : R) :
    ((X - C a) ^ 2 + C b ^ 2).Monic := by
  rw [show ((X - C a) ^ 2 + C b ^ 2) = (X ^ 2 + C b ^ 2).comp (X - C a) by simp,
      Monic, Polynomial.leadingCoeff_comp (by simp)]
  simp [← map_pow]

open scoped Polynomial in
theorem Polynomial.exists_odd_natDegree_monic_irreducible_factor
    {F : Type*} [Field F] {f : F[X]} (hf : Odd f.natDegree) :
    ∃ g : F[X], (Odd g.natDegree) ∧ g.Monic ∧ Irreducible g ∧ g ∣ f := by
  induction h : f.natDegree using Nat.strong_induction_on generalizing f with | h n ih =>
    have hu : ¬IsUnit f := Polynomial.not_isUnit_of_natDegree_pos _ (Odd.pos hf)
    rcases Polynomial.exists_monic_irreducible_factor f hu with ⟨g, g_monic, g_irred, g_div⟩
    by_cases g_deg : Odd g.natDegree
    · exact ⟨g, g_deg, g_monic, g_irred, g_div⟩
    · rcases g_div with ⟨k, hk⟩
      have : f.natDegree = g.natDegree + k.natDegree := by
        simpa [hk] using Polynomial.natDegree_mul (g_irred.ne_zero) (fun _ ↦ by simp_all)
      have := Irreducible.natDegree_pos g_irred
      rcases ih k.natDegree (by omega) (by grind) rfl with ⟨l, h₁, h₂, h₃, h₄⟩
      exact ⟨l, h₁, h₂, h₃, dvd_trans h₄ (dvd_iff_exists_eq_mul_left.mpr ⟨g, hk⟩)⟩

open scoped Polynomial in
theorem Polynomial.has_root_of_odd_natDegree_imp_not_irreducible {F : Type*} [Field F]
    (h : ∀ f : F[X], Odd f.natDegree → f.natDegree ≠ 1 → ¬(Irreducible f))
    {f : F[X]} (hf : Odd f.natDegree) : ∃ x, f.IsRoot x := by
  induction hdeg : f.natDegree using Nat.strong_induction_on generalizing f with | h n ih =>
    rcases hdeg with rfl
    have : f ≠ 0 := fun _ ↦ by simp_all
    by_cases hdeg1 : f.natDegree = 1
    · simp_rw [← Polynomial.mem_roots ‹f ≠ 0›]
      rw [Polynomial.roots_degree_eq_one
        (by simpa [Polynomial.natDegree_eq_one_iff_degree_eq_one] using hdeg1)]
      simp
    · rcases (by simpa [h _ hf hdeg1] using
          irreducible_or_factor (Polynomial.not_isUnit_of_natDegree_pos f (Odd.pos hf))) with
        ⟨a, ha, b, hb, hfab⟩
      have : a ≠ 0 := fun _ ↦ by simp_all
      have : b ≠ 0 := fun _ ↦ by simp_all
      have hsum : f.natDegree = a.natDegree + b.natDegree := by
        simpa [hfab] using Polynomial.natDegree_mul ‹_› ‹_›
      have hodd : Odd a.natDegree ∨ Odd b.natDegree := by grind
      wlog h : Odd a.natDegree generalizing a b
      · exact this b ‹_› a ‹_› (by simpa [mul_comm] using hfab) ‹_› ‹_›
          (by simpa [add_comm] using hsum) (by simp_all) (by simpa [h] using hodd)
      · have : b.natDegree ≠ 0 := fun hc ↦ by
          rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree ‹_›] at hb
          exact hb (by simpa using hc)
        rcases ih a.natDegree (by omega) h rfl with ⟨r, hr⟩
        exact ⟨r, Polynomial.IsRoot.dvd hr (by simp [hfab])⟩

open scoped Polynomial in
open Classical in -- for `normalize` instance
theorem Polynomial.has_root_of_monic_odd_natDegree_imp_not_irreducible {F : Type*} [Field F]
    (h : ∀ f : F[X], f.Monic → Odd f.natDegree → f.natDegree ≠ 1 → ¬(Irreducible f))
    {f : F[X]} (hf : Odd f.natDegree) : ∃ x, f.IsRoot x := by
  refine has_root_of_odd_natDegree_imp_not_irreducible (fun f hf₁ hf₂ hf₃ ↦ ?_) hf
  exact h (normalize f) (Polynomial.monic_normalize (Irreducible.ne_zero hf₃))
    (by simpa using hf₁) (by simpa using hf₂)
    (by rw [Associated.irreducible_iff (normalize_associated f)]; exact hf₃)

section poly_estimate

open Polynomial
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] (f : F[X])

open Finset in
variable {f} in
theorem estimate (hdeg : f.natDegree ≠ 0) {x : F} (hx : 1 ≤ x) :
    x ^ (f.natDegree - 1) * (f.leadingCoeff * x -
      f.natDegree * (image (|f.coeff ·|) (range f.natDegree)).max'
        (by simpa using hdeg)) ≤ f.eval x := by
  generalize_proofs ne
  set M := (image (|f.coeff ·|) (range f.natDegree)).max' ne
  have hM : ∀ i < f.natDegree, |f.coeff i| ≤ M := fun i hi ↦
    le_max' _ _ <| mem_image_of_mem (|f.coeff ·|) (by simpa using hi)
  have hM₀ : 0 ≤ M := (abs_nonneg _).trans (hM 0 (by omega))
  rw [Polynomial.eval_eq_sum_range, sum_range_succ, ← leadingCoeff]
  suffices f.natDegree * (-M * x ^ (f.natDegree - 1)) ≤
           ∑ i ∈ range f.natDegree, f.coeff i * x ^ i by
    have hxpow : x * x ^ (f.natDegree - 1) = x ^ f.natDegree := by
      rw [← pow_succ', show f.natDegree - 1 + 1 = f.natDegree by omega]
    linear_combination this + hxpow * f.leadingCoeff
  suffices ∀ i < f.natDegree, -M * x ^ (f.natDegree - 1) ≤ f.coeff i * x ^ i by
    simpa using card_nsmul_le_sum (range f.natDegree) (fun i ↦ f.coeff i * x ^ i)
      (-M * x ^ (f.natDegree - 1)) (by simpa using this)
  intro i hi
  calc
    -M * x ^ (f.natDegree - 1) ≤ -M * x ^ i :=
      mul_le_mul_of_nonpos_left (by gcongr; exacts [hx, by omega]) (by simpa using hM₀)
    _ ≤ f.coeff i * x ^ i := by gcongr; exact neg_le_of_abs_le (hM _ hi)

variable {f} in
theorem eventually_pos (hdeg : f.natDegree ≠ 0) (hf : 0 < f.leadingCoeff) :
    ∃ y : F, ∀ x, y < x → 0 < f.eval x := by
  set z := (Finset.image (|f.coeff ·|) (Finset.range f.natDegree)).max' (by simpa using hdeg)
  use max 1 (f.natDegree * z / f.leadingCoeff)
  intro x hx
  have one_lt_x : 1 < x := lt_of_le_of_lt (le_max_left ..) hx
  have := calc
    f.eval x ≥ x ^ (f.natDegree - 1) * (f.leadingCoeff * x - f.natDegree * z) :=
      estimate hdeg (le_of_lt one_lt_x)
    _ > x ^ (f.natDegree - 1) * (f.leadingCoeff * (max 1 (f.natDegree * z / f.leadingCoeff)) -
        f.natDegree * z) := by gcongr
    _ ≥ x ^ (f.natDegree - 1) * (f.leadingCoeff * (f.natDegree * z / f.leadingCoeff) -
        f.natDegree * z) := by gcongr; exact le_max_right ..
  field_simp at this
  ring_nf at this
  assumption

open Finset in
variable {f} in
theorem estimate2 (hdeg : Odd f.natDegree) {x : F} (hx : x ≤ -1) :
    f.eval x ≤ x ^ (f.natDegree - 1) * (f.leadingCoeff * x +
      f.natDegree * (image (|f.coeff ·|) (range f.natDegree)).max'
        (by simpa using Nat.ne_of_odd_add hdeg)) := by
  generalize_proofs ne
  have : f.natDegree ≠ 0 := Nat.ne_of_odd_add hdeg
  set M := (image (|f.coeff ·|) (range f.natDegree)).max' ne
  have hM : ∀ i < f.natDegree, |f.coeff i| ≤ M := fun i hi ↦
    le_max' _ _ <| mem_image_of_mem (|f.coeff ·|) (by simpa using hi)
  have hM₀ : 0 ≤ M := (abs_nonneg _).trans (hM 0 (by omega))
  rw [Polynomial.eval_eq_sum_range, sum_range_succ, ← leadingCoeff]
  suffices ∑ i ∈ range f.natDegree, f.coeff i * x ^ i ≤
           f.natDegree * (M * x ^ (f.natDegree - 1)) by
    have hxpow : x ^ f.natDegree = x * x ^ (f.natDegree - 1) := by
      rw [← pow_succ', show f.natDegree - 1 + 1 = f.natDegree by omega]
    linear_combination this + hxpow * f.leadingCoeff
  suffices ∀ i < f.natDegree, f.coeff i * x ^ i ≤ M * x ^ (f.natDegree - 1) by
    simpa using sum_le_card_nsmul (range f.natDegree) (fun i ↦ f.coeff i * x ^ i) _ <|
      by simpa using this
  intro i hi
  rw [← Even.pow_abs <| Nat.Odd.sub_odd hdeg (by simp)]
  calc
    f.coeff i * x ^ i ≤ |f.coeff i| * |x| ^ i := by
      rw [← abs_pow, ← abs_mul]
      exact le_abs_self ..
    _ ≤ M * |x| ^ (f.natDegree - 1) := by
      gcongr; exacts [hM _ hi, by simpa using abs_le_abs_of_nonpos (by linarith) hx, by omega]

variable {f} in
theorem eventually_neg (hdeg : Odd f.natDegree) (hf : 0 < f.leadingCoeff) :
    ∃ y : F, ∀ x, x < y → f.eval x < 0 := by
  set z := (Finset.image (|f.coeff ·|) (Finset.range f.natDegree)).max'
    (by simpa using Nat.ne_of_odd_add hdeg)
  use min (-1) (-f.natDegree * z / f.leadingCoeff)
  intro x hx
  have one_lt_x : x < -1 := lt_of_lt_of_le hx (min_le_left ..)
  have : 0 < x ^ (f.natDegree - 1) := by
    rw [← Even.pow_abs <| Nat.Odd.sub_odd hdeg (by simp)]
    have : 1 ≤ |x| := by simpa using abs_le_abs_of_nonpos (by linarith) (by linarith: x ≤ -1)
    positivity
  have := calc
    f.eval x ≤ x ^ (f.natDegree - 1) * (f.leadingCoeff * x + f.natDegree * z) :=
      estimate2 hdeg (le_of_lt one_lt_x)
    _ < x ^ (f.natDegree - 1) * (f.leadingCoeff * (min (-1) (-f.natDegree * z / f.leadingCoeff)) +
        f.natDegree * z) := by gcongr
    _ ≤ x ^ (f.natDegree - 1) * (f.leadingCoeff * (-f.natDegree * z / f.leadingCoeff) +
        f.natDegree * z) := by gcongr; exact min_le_right ..
  field_simp at this
  ring_nf at this
  assumption

variable {f} in
theorem sign_change (hdeg: Odd f.natDegree) : ∃ x y, f.eval x < 0 ∧ 0 < f.eval y := by
  wlog hf : 0 < f.leadingCoeff generalizing f with res
  · have : 0 < (-f).leadingCoeff := by linarith (config := { splitNe := true })
      [show f.leadingCoeff ≠ 0 from fun _ ↦ by simp_all, leadingCoeff_neg f]
    rcases res (by simpa using hdeg) this with ⟨x, y, hx, hy⟩
    exact ⟨y, x, by simp_all⟩
  · rcases eventually_pos (fun _ ↦ by simp_all) hf with ⟨x, hx⟩
    rcases eventually_neg hdeg hf with ⟨y, hy⟩
    exact ⟨y-1, x+1, hy _ (by linarith), hx _ (by linarith)⟩

end poly_estimate

theorem Module.finrank_dvd_finrank (F K A : Type*) [Semiring F] [Ring K] [AddCommGroup A]
    [Module F K] [Module K A] [Module F A] [IsScalarTower F K A] [Nontrivial A]
    [StrongRankCondition F] [StrongRankCondition K] [Module.Free F K] [Module.Free K A]
    [Module.Finite K A] [NoZeroSMulDivisors K A] :
    Module.finrank F K = Module.finrank F A / Module.finrank K A :=
  Nat.eq_div_of_mul_eq_left finrank_pos.ne' (finrank_mul_finrank ..)

theorem Module.finrank_dvd_finrank' (F K A : Type*) [Ring F] [Ring K] [AddCommMonoid A]
    [Module F K] [Module K A] [Module F A] [IsScalarTower F K A] [Nontrivial K]
    [StrongRankCondition F] [StrongRankCondition K] [Module.Free F K] [Module.Free K A]
    [Module.Finite F K] [NoZeroSMulDivisors F K] :
    Module.finrank K A = Module.finrank F A / Module.finrank F K :=
  Nat.eq_div_of_mul_eq_right finrank_pos.ne' (finrank_mul_finrank ..)

theorem IsGalois.exists_intermediateField_of_pow_prime_dvd
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {p n : ℕ} (hp : Nat.Prime p) (hn : p ^ n ∣ Module.finrank K L):
    ∃ M : IntermediateField K L, Module.finrank M L = p ^ n := by
  have := Fact.mk hp
  rw [← IsGalois.card_aut_eq_finrank K L] at hn
  rcases Sylow.exists_subgroup_card_pow_prime p hn with ⟨H, hH⟩
  exact ⟨IntermediateField.fixedField H,
        by simpa [IntermediateField.finrank_fixedField_eq_card] using hH⟩

theorem IsGalois.exists_intermediateField_of_card_pow_prime_mul
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {p n a : ℕ} (hp : Nat.Prime p) (hn : Module.finrank K L = p ^ n * a) {m : ℕ} (hm : m ≤ n) :
    ∃ M : IntermediateField K L, Module.finrank K M = p ^ m * a := by
  rcases IsGalois.exists_intermediateField_of_pow_prime_dvd hp
    (by rw [hn]; exact Nat.pow_dvd_of_le_of_pow_dvd (by simp : n - m ≤ n) (by simp)) with ⟨M, hM⟩
  use M
  have dvd := Module.finrank_dvd_finrank K M L
  rw [hn, hM, ← Nat.pow_sub_mul_pow _ hm, mul_assoc,
      Nat.mul_div_right _ (by positivity [hp.pos])] at dvd
  exact dvd

theorem Sylow.exists_subgroup_le_card_pow_prime_of_card_pow_prime
    {G : Type*} [Group G] {m n p : ℕ} (hp : Nat.Prime p)
    {H : Subgroup G} (hH : Nat.card H = p ^ n) (hm : m ≤ n) :
    ∃ H' ≤ H, Nat.card H' = p ^ m := by
  have : p ^ m ≤ Nat.card H := by
    rw [hH]
    gcongr
    exact Nat.Prime.one_le hp
  rcases Sylow.exists_subgroup_card_pow_prime_of_le_card hp (IsPGroup.of_card hH) this with ⟨H', hH'⟩
  refine ⟨H'.map H.subtype, Subgroup.map_subtype_le .., ?_⟩
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective H)]
  exact hH'

theorem IsGalois.exists_intermediateField_ge_card_pow_prime_of_card_pow_prime
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {m n p : ℕ} (hp : Nat.Prime p) {M : IntermediateField K L}
    (hM : Module.finrank M L = p ^ n) (hm : m ≤ n) :
    ∃ N ≥ M, Module.finrank N L = p ^ m := by
  rcases Sylow.exists_subgroup_le_card_pow_prime_of_card_pow_prime (H := M.fixingSubgroup)
    hp (by rw [IsGalois.card_fixingSubgroup_eq_finrank, hM]) hm with
    ⟨H', hH'₁, hH'₂⟩
  exact ⟨IntermediateField.fixedField H',
        by simpa [IntermediateField.le_iff_le] using hH'₁,
        by simpa [IntermediateField.finrank_fixedField_eq_card] using hH'₂⟩

theorem IsGalois.exists_intermediateField_ge_card_pow_prime_mul_of_card_pow_prime_mul
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {p n a : ℕ} (hp : Nat.Prime p) (hL : Module.finrank K L = p ^ n * a)
    {m m' : ℕ} {M : IntermediateField K L} (hM : Module.finrank K M = p ^ m * a)
    (hm'₁ : m ≤ m') (hm'₂ : m' ≤ n) :
    ∃ N ≥ M, Module.finrank K N = p ^ m' * a := by
  by_cases! haz : a = 0
  · exact ⟨M, by simp, by simp_all⟩
  have : 0 < p := hp.pos
  have : Module.finrank (↥M) L = p ^ (n - m) := by
    have dvd := Module.finrank_dvd_finrank' K M L
    rw [hM, hL, ← Nat.pow_sub_mul_pow _ (by omega : m ≤ n), mul_assoc,
        Nat.mul_div_left _ (by positivity)] at dvd
    exact dvd
  rcases IsGalois.exists_intermediateField_ge_card_pow_prime_of_card_pow_prime hp (M := M)
    (n := n - m) (m := n - m') this (by omega) with ⟨N, hN, hNrk⟩
  refine ⟨N, hN, ?_⟩
  have dvd := Module.finrank_dvd_finrank K N L
  rw [hL, hNrk, ← Nat.pow_sub_mul_pow _ hm'₂, mul_assoc,
      Nat.mul_div_right _ (by positivity)] at dvd
  exact dvd

-- `Algebra.Order.Module.Algebra`
theorem IsOrderedModule.of_algebraMap_mono {R A : Type*} [CommSemiring R] [Preorder R]
    [Semiring A] [PartialOrder A] [PosMulMono A] [MulPosMono A] [Algebra R A]
    (h : Monotone (algebraMap R A)) : IsOrderedModule R A where
  smul_le_smul_of_nonneg_left _ ha _ _ hb := by
    simpa [Algebra.smul_def] using mul_le_mul_of_nonneg_left hb (by simpa using h ha)
  smul_le_smul_of_nonneg_right _ ha _ _ hb := by
    simpa [Algebra.smul_def] using mul_le_mul_of_nonneg_right (h hb) ha

theorem Module.nonempty_algEquiv_iff_finrank_eq_one
    {R S : Type*} [CommSemiring R] [StrongRankCondition R] [Semiring S] [Algebra R S]
    [Module.Free R S] : Nonempty (R ≃ₐ[R] S) ↔ Module.finrank R S = 1 where
  mp h := by
    rw [← Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _) h.some.toRingEquiv (by ext; simp)]
    simp
  mpr h := ⟨AlgEquiv.ofBijective (Algebra.ofId R S)
    (bijective_algebraMap_of_linearEquiv (Module.nonempty_linearEquiv_of_finrank_eq_one h).some)⟩

theorem IsAlgClosed.isSquare {k : Type*} [Field k] [IsAlgClosed k] (x : k) : IsSquare x :=
  IsAlgClosed.exists_eq_mul_self x

theorem IsAlgClosed.of_finiteDimensional_imp_finrank_eq_one (k : Type u) [Field k]
    (H : ∀ (l : Type u), [Field l] → [Algebra k l] → [FiniteDimensional k l] →
          Module.finrank k l = 1) :
    IsAlgClosed k :=
  .of_exists_root _ fun f f_monic f_irr ↦ by
    have := Fact.mk f_irr
    have := f_monic.finite_adjoinRoot
    have := H (AdjoinRoot f)
    rw [← Module.nonempty_algEquiv_iff_finrank_eq_one] at this
    use this.some.symm (AdjoinRoot.root f)
    rw [← Polynomial.coe_aeval_eq_eval, Polynomial.aeval_algHom_apply]
    simp
