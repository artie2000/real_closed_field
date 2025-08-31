/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib

/- Lemmas that should be upstreamed to Mathlib -/

@[aesop unsafe 70%]
theorem mem_of_mem_sup_left {R : Type*} [Semiring R] {a b : Subsemiring R} {x : R} :
    x ∈ a → x ∈ a ⊔ b := by gcongr; exact le_sup_left

@[aesop unsafe 70%]
theorem mem_of_mem_sup_right {R : Type*} [Semiring R] {a b : Subsemiring R} {x : R} :
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

open Polynomial in
theorem X_sq_sub_C_irreducible_iff_not_isSquare {F : Type*} [Field F] (a : F) :
    Irreducible (X ^ 2 - C a) ↔ ¬ IsSquare a := by
  rw [isSquare_iff_exists_sq, X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two]
  grind only

-- TODO : remove AdjoinRoot.of
attribute [-simp] AdjoinRoot.algebraMap_eq

-- PRed as change to Module.Basis.repr_algebraMap
theorem Module.Basis.repr_algebraMap'
    {R : Type*} {S : Type*} [CommRing R] [Ring S] [Algebra R S]
    {ι : Type*} [DecidableEq ι] {B : Module.Basis ι R S} {i : ι} (hBi : B i = 1)
    (r : R) : B.repr ((algebraMap R S) r) = Finsupp.single i r := by
  ext j; simp [Algebra.algebraMap_eq_smul_one, ← hBi]

namespace PowerBasis

open scoped algebraMap

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S] [Nontrivial S] (pb : PowerBasis R S)

instance : NeZero pb.dim := NeZero.mk pb.dim_ne_zero

-- TODO : rewrite proofs in IsAdjoinRoot using these
@[simp]
theorem repr_algebraMap (x : R) : pb.basis.repr x = Finsupp.single 0 x :=
  Module.Basis.repr_algebraMap' (by simp : pb.basis 0 = 1) x

@[simp]
theorem repr_ofNat (n : ℕ) [Nat.AtLeastTwo n] :
    pb.basis.repr ofNat(n) = Finsupp.single 0 (n : R) := by
  simpa [map_ofNat] using repr_algebraMap pb ofNat(n)

end PowerBasis

namespace IsAdjoinRoot

open _root_.Polynomial

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S] {f : R[X]} (hf : IsAdjoinRoot S f)

-- TODO : remove IsAdjoinRoot.algebraMap_apply

@[simp]
theorem map_C {x} : hf.map (C x) = algebraMap _ _ x := by rw [← algebraMap_apply]

include hf in
theorem nontrivial [IsDomain R] (h : f.degree ≠ 0) : Nontrivial S :=
  hf.adjoinRootAlgEquiv.nontrivial_congr.mp <| AdjoinRoot.nontrivial f h

end IsAdjoinRoot

namespace IsAdjoinRoot

open _root_.Polynomial

variable {R F : Type*} [CommRing R] [Field F] [Algebra R F] {f : R[X]} (hf : IsAdjoinRoot F f)

include hf in
theorem ne_zero : f ≠ 0 := fun _ ↦ Polynomial.not_isField R <|
  MulEquiv.isField (Field.toIsField F) <|
    (RingEquiv.quotientBot _).symm.trans <|
    (Ideal.quotientEquiv ⊥ (Ideal.span {f}) (RingEquiv.refl _) (by simpa)).trans <|
    hf.adjoinRootAlgEquiv.toRingEquiv

include hf in
theorem irreducible [IsDomain R] : Irreducible f :=
  Ideal.Quotient.irreducible_of_isField hf.ne_zero <|
    hf.adjoinRootAlgEquiv.toMulEquiv.isField (Field.toIsField F)

end IsAdjoinRoot

namespace IsAdjoinRootMonic

open _root_.Polynomial

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S] {f : R[X]} (hf : IsAdjoinRootMonic S f)

include hf in
theorem nontrivial (h : f ≠ 1) : Nontrivial S :=
  hf.adjoinRootAlgEquiv.nontrivial_congr.mp <| Ideal.Quotient.nontrivial <| by
    simpa using (h <| Monic.eq_one_of_isUnit hf.monic ·)

theorem coeff_ofNat [Nontrivial S] (n : ℕ) [Nat.AtLeastTwo n] :
    hf.coeff ofNat(n) = Pi.single 0 (n : R) := by simpa using hf.coeff_algebraMap n

theorem coeff_modByMonicHom : Polynomial.coeff ∘ hf.modByMonicHom = hf.coeff := by
  simp [coeff, IsAdjoinRootMonic.liftPolyₗ]

@[simp]
theorem coeff_modByMonicHom_apply {x} : (hf.modByMonicHom x).coeff = hf.coeff x := by
  simp [← coeff_modByMonicHom]

end IsAdjoinRootMonic

section Field.isAdjoinRootMonic

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
         [FiniteDimensional F E] [Algebra.IsSeparable F E]

open Polynomial

variable (F E) in
noncomputable def Field.isAdjoinRootMonic : Σ f : F[X], IsAdjoinRootMonic E f :=
  let ⟨α, hα⟩ := Classical.indefiniteDescription _ <| Field.exists_primitive_element F E
  ⟨_, IsAdjoinRootMonic.mkOfPrimitiveElement (Algebra.IsIntegral.isIntegral α) hα⟩

end Field.isAdjoinRootMonic

namespace IsAdjoinRoot.Quadratic

open _root_.Polynomial
open scoped algebraMap

variable {K L : Type*} [CommRing K] [CommRing L] [Algebra K L]
         {a : K} (hL : IsAdjoinRootMonic L (X ^ 2 - C a))

set_option quotPrecheck false in
scoped notation "√a" => hL.root -- TODO : figure out how to use this notation elsewhere

@[simp]
theorem sq_root : √a ^ 2 = a := by
  suffices √a ^ 2 - a = 0 by simpa [sub_eq_zero]
  simpa [-map_self] using hL.map_self

variable [Nontrivial K]

instance : NeZero (X ^ 2 - C a).natDegree := ⟨by simp⟩

include hL in
theorem nontrivial : Nontrivial L := hL.nontrivial (by apply_fun natDegree; simp)

include hL in
theorem isQuadraticExtension : Algebra.IsQuadraticExtension K L where
  __ := Module.Free.of_basis hL.basis
  finrank_eq_two' := by simpa using hL.finrank

theorem basis_0 : hL.basis 0 = 1 := by simp

theorem basis_1 : hL.basis 1 = √a := by simp

@[simp]
theorem coeff_one : hL.coeff 1 = Pi.single 0 1 :=
  letI _ := nontrivial hL
  hL.coeff_one

@[simp]
theorem coeff_root : hL.coeff √a = Pi.single 1 1 := hL.coeff_root (by simp)

@[simp]
theorem coeff_algebraMap (x : K) : hL.coeff x = Pi.single 0 x :=
  letI _ := nontrivial hL
  hL.coeff_algebraMap x

@[simp]
theorem coeff_ofNat (n : ℕ) [Nat.AtLeastTwo n] : hL.coeff ofNat(n) = Pi.single 0 (n : K) :=
  letI _ := nontrivial hL
  hL.coeff_ofNat n

theorem self_eq_coeff (x) :
    x = hL.coeff x 0 + hL.coeff x 1 * √a := by
  rw [hL.ext_elem_iff]
  intro i hi
  simp_rw [show (X ^ 2 - C a).natDegree = 2 by simp] at hi
  interval_cases i <;> simp [← Algebra.smul_def]

theorem coeff_of_add_of_mul_root {x y : K} :
    hL.coeff (x + y * (√a)) = fun₀ | 0 => x | 1 => y := by
  ext i
  by_cases h : i < 2
  · interval_cases i <;> simp [← Algebra.smul_def]
  · rw [show hL.coeff _ i = 0 from hL.coeff_apply_le _ i (by simpa using h)]
    simp [show 0 ≠ i ∧ i ≠ 1 by omega]

@[simp]
theorem coeff_mul (x y) : hL.coeff (x * y) =
    fun₀
    | 0 => hL.coeff x 0 * hL.coeff y 0 + a * hL.coeff x 1 * hL.coeff y 1
    | 1 => hL.coeff x 0 * hL.coeff y 1 + hL.coeff y 0 * hL.coeff x 1 := by
  rw [← coeff_of_add_of_mul_root hL]
  congr
  nth_rw 1 [self_eq_coeff hL x, self_eq_coeff hL y]
  ring_nf
  simp only [sq_root, map_mul, map_add]
  ring

end IsAdjoinRoot.Quadratic

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
      rw [Polynomial.eq_X_add_C_of_degree_eq_one
            (show f.degree = 1 by simpa [Polynomial.degree_eq_natDegree ‹f ≠ 0›] using hdeg1),
          Polynomial.roots_C_mul_X_add_C _ (by simp [‹f ≠ 0›])]
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
