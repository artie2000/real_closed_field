import Mathlib.Algebra.Group.Submonoid.Support
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Ring.Subsemiring.Order
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Sylow

/- Lemmas that should be upstreamed to Mathlib -/

-- #44253
@[aesop 70%]
theorem mem_sup_left {R : Type*} [Semiring R] {a b : Subsemiring R} {x : R} :
    x ∈ a → x ∈ a ⊔ b := by gcongr; exact le_sup_left

-- #44253
@[aesop 70%]
theorem mem_sup_right {R : Type*} [Semiring R] {a b : Subsemiring R} {x : R} :
    x ∈ b → x ∈ a ⊔ b := by gcongr; exact le_sup_right

-- #44287
@[simp]
theorem irreducible_normalize_iff {α : Type*}
    [CommMonoidWithZero α] [IsCancelMulZero α] [NormalizationMonoid α] (x : α) :
    Irreducible (normalize x) ↔ Irreducible x :=
  Associated.irreducible_iff (normalize_associated x)

-- #44287
open scoped Polynomial in
theorem Polynomial.exists_odd_natDegree_monic_irreducible_factor
    {F : Type*} [Field F] {f : F[X]} (hf : Odd f.natDegree) :
    ∃ g : F[X], (Odd g.natDegree) ∧ g.Monic ∧ Irreducible g ∧ g ∣ f := by
  induction h : f.natDegree using Nat.strong_induction_on generalizing f with | h n ih =>
    have hu : ¬ IsUnit f := not_isUnit_of_natDegree_pos _ (Odd.pos hf)
    rcases exists_monic_irreducible_factor f hu with ⟨g, g_monic, g_irred, g_div⟩
    by_cases g_deg : Odd g.natDegree
    · exact ⟨g, g_deg, g_monic, g_irred, g_div⟩
    · rcases g_div with ⟨k, rfl⟩
      have : (g * k).natDegree = g.natDegree + k.natDegree := natDegree_mul (by grind) (by grind)
      rcases ih k.natDegree (by lia [Irreducible.natDegree_pos]) (by grind) rfl
        with ⟨l, h₁, h₂, h₃, h₄⟩
      exact ⟨l, h₁, h₂, h₃, dvd_trans h₄ (by simp)⟩

-- #44287
open scoped Polynomial in
theorem Polynomial.exists_root_of_odd_natDegree_imp_not_irreducible {F : Type*} [Field F]
    (h : ∀ {g : F[X]}, Odd g.natDegree → g.natDegree ≠ 1 → ¬ Irreducible g)
    {f : F[X]} (hf : Odd f.natDegree) : ∃ x, f.IsRoot x := by
  induction hdeg : f.natDegree using Nat.strong_induction_on generalizing f with | h n ih =>
    subst hdeg
    by_cases hdeg1 : f.natDegree = 1
    · exact exists_root_of_degree_eq_one <| by
        simpa [← degree_eq_iff_natDegree_eq_of_neZero] using hdeg1
    · rcases irreducible_or_factor (not_isUnit_of_natDegree_pos f (by grind)) with
          _ | ⟨a, b, ha, hb, rfl⟩
      · grind
      have hsum : (a * b).natDegree = a.natDegree + b.natDegree :=
        natDegree_mul (by grind) (by grind)
      wlog h : Odd a.natDegree generalizing a b
      · rw [mul_comm, add_comm] at *
        apply this b a <;> grind
      · have : b.natDegree ≠ 0 := fun _ ↦ by
          simp_all [isUnit_iff_degree_eq_zero, degree_eq_natDegree (show b ≠ 0 by grind)]
        rcases ih a.natDegree (by lia) h rfl with ⟨r, hr⟩
        exact ⟨r, hr.dvd (by simp)⟩

-- #44287
open scoped Polynomial in
open Classical in -- for `normalize` instance
theorem Polynomial.exists_root_of_monic_odd_natDegree_imp_not_irreducible {F : Type*} [Field F]
    (h : ∀ {g : F[X]}, g.Monic → Odd g.natDegree → g.natDegree ≠ 1 → ¬ Irreducible g)
    {f : F[X]} (hf : Odd f.natDegree) : ∃ x, f.IsRoot x := by
  refine exists_root_of_odd_natDegree_imp_not_irreducible (fun {f} hf₁ hf₂ hf₃ ↦ ?_) hf
  exact h (monic_normalize (Irreducible.ne_zero hf₃))
    (by simpa using hf₁) (by simpa using hf₂) (by simpa using hf₃)

-- #44299
theorem IsGalois.exists_intermediateField_of_pow_prime_dvd
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {p n : ℕ} (hp : Nat.Prime p) (hn : p ^ n ∣ Module.finrank K L) :
    ∃ M : IntermediateField K L, Module.finrank M L = p ^ n := by
  have := Fact.mk hp
  rw [← IsGalois.card_aut_eq_finrank K L] at hn
  rcases Sylow.exists_subgroup_card_pow_prime p hn with ⟨H, hH⟩
  exact ⟨IntermediateField.fixedField H,
        by simpa [IntermediateField.finrank_fixedField_eq_card] using hH⟩

-- #44299
theorem IsGalois.exists_intermediateField_of_card_pow_prime_mul
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {p n a : ℕ} (hp : Nat.Prime p) (hn : Module.finrank K L = p ^ n * a) {m : ℕ} (hm : m ≤ n) :
    ∃ M : IntermediateField K L, Module.finrank K M = p ^ m * a := by
  rcases IsGalois.exists_intermediateField_of_pow_prime_dvd hp
    (by rw [hn]; exact Nat.pow_dvd_of_le_of_pow_dvd (by simp : n - m ≤ n) (by simp)) with ⟨M, hM⟩
  use M
  rw [← Module.finrank_div_finrank_cancel_right_of_nontrivial _ _ L, hn, hM,
      ← Nat.pow_sub_mul_pow _ hm, mul_assoc, Nat.mul_div_right _ (by positivity [hp.pos])]

-- #44299
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

-- #44299
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

-- #44299
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
    rw [← Module.finrank_div_finrank_cancel_left_of_nontrivial K, hM, hL,
        ← Nat.pow_sub_mul_pow _ (by lia : m ≤ n), mul_assoc, Nat.mul_div_left _ (by positivity)]
  rcases IsGalois.exists_intermediateField_ge_card_pow_prime_of_card_pow_prime hp (M := M)
    (n := n - m) (m := n - m') this (by lia) with ⟨N, hN, hNrk⟩
  refine ⟨N, hN, ?_⟩
  rw [← Module.finrank_div_finrank_cancel_right_of_nontrivial _ _ L, hL, hNrk,
      ← Nat.pow_sub_mul_pow _ hm'₂, mul_assoc, Nat.mul_div_right _ (by positivity)]

-- #44309
theorem IsAlgClosed.isSquare {k : Type*} [Field k] [IsAlgClosed k] (x : k) : IsSquare x :=
  IsAlgClosed.exists_eq_mul_self x

-- #44310
theorem IsAlgClosed.of_finiteDimensional_imp_finrank_eq_one.{u} (k : Type u) [Field k]
    (H : ∀ (l : Type u), [Field l] → [Algebra k l] → [FiniteDimensional k l] →
          Module.finrank k l = 1) :
    IsAlgClosed k :=
  .of_exists_root _ fun f f_monic f_irr ↦ by
    have := Fact.mk f_irr
    have := f_monic.finite_adjoinRoot
    have := H (AdjoinRoot f)
    rw [← Module.nonempty_algEquiv_iff_finrank_eq_one] at this
    use this.some.symm (AdjoinRoot.root f)
    simp [← Polynomial.coe_aeval_eq_eval, Polynomial.aeval_algHom_apply]

-- begin #44311
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
  have hM₀ : 0 ≤ M := (abs_nonneg _).trans (hM 0 (by lia))
  rw [Polynomial.eval_eq_sum_range, sum_range_succ, ← leadingCoeff]
  suffices f.natDegree * (-M * x ^ (f.natDegree - 1)) ≤
           ∑ i ∈ range f.natDegree, f.coeff i * x ^ i by
    have hxpow : x * x ^ (f.natDegree - 1) = x ^ f.natDegree := by
      rw [← pow_succ', show f.natDegree - 1 + 1 = f.natDegree by lia]
    linear_combination this + hxpow * f.leadingCoeff
  suffices ∀ i < f.natDegree, -M * x ^ (f.natDegree - 1) ≤ f.coeff i * x ^ i by
    simpa using card_nsmul_le_sum (range f.natDegree) (fun i ↦ f.coeff i * x ^ i)
      (-M * x ^ (f.natDegree - 1)) (by simpa using this)
  intro i hi
  calc
    -M * x ^ (f.natDegree - 1) ≤ -M * x ^ i :=
      mul_le_mul_of_nonpos_left (by gcongr; lia) (by simpa using hM₀)
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
  have hM₀ : 0 ≤ M := (abs_nonneg _).trans (hM 0 (by lia))
  rw [Polynomial.eval_eq_sum_range, sum_range_succ, ← leadingCoeff]
  suffices ∑ i ∈ range f.natDegree, f.coeff i * x ^ i ≤
           f.natDegree * (M * x ^ (f.natDegree - 1)) by
    have hxpow : x ^ f.natDegree = x * x ^ (f.natDegree - 1) := by
      rw [← pow_succ', show f.natDegree - 1 + 1 = f.natDegree by lia]
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
      gcongr; exacts [hM _ hi, by simpa using abs_le_abs_of_nonpos (by linarith) hx, by lia]

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
-- end #44311

namespace IsFormallyReal

variable {R : Type*}

-- #44288
@[simp]
theorem Subsemiring.sumSq_toAddSubmonoid {T : Type*} [CommSemiring T] :
    (Subsemiring.sumSq T).toAddSubmonoid = .sumSq T := by ext; simp

-- #44288
variable (R) in
protected theorem AddSubmonoid.IsPointed.sumSq [CommRing R] [IsFormallyReal R] :
    (AddSubmonoid.sumSq R).IsPointed := fun _ ↦ by
  simpa using IsFormallyReal.eq_zero_of_isSumSq_of_neg_isSumSq

-- #44288
variable (R) in
protected theorem Subsemiring.IsPointed.sumSq [CommRing R] [IsFormallyReal R] :
    (Subsemiring.sumSq R).IsPointed := by
  simpa using AddSubmonoid.IsPointed.sumSq R

end IsFormallyReal

-- begin #37252
namespace Submonoid

section Group

variable {G H : Type*} [Group G] [Group H] (f : G →* H) (M N : Submonoid G) (M' : Submonoid H)
         {s : Set (Submonoid G)}

@[to_additive (attr := simp)]
theorem mulSupport_bot : (⊥ : Submonoid G).mulSupport = ⊥ := by ext; simp

@[to_additive (attr := simp)]
theorem mulSupport_top : (⊤ : Submonoid G).mulSupport = ⊤ := by ext; simp

variable {M N} in
@[to_additive]
theorem mulSupport_mono (h : M ≤ N) : M.mulSupport ≤ N.mulSupport := fun _ ↦ by
  have := mem_of_le_of_mem h
  grind [mem_mulSupport]

@[to_additive (attr := simp)]
theorem mulSupport_inf : (M ⊓ N).mulSupport = M.mulSupport ⊓ N.mulSupport := by
  ext
  grind [mem_mulSupport, Subgroup.mem_inf]

@[to_additive (attr := simp)]
theorem mulSupport_sInf (s : Set (Submonoid G)) :
    (sInf s).mulSupport = InfSet.sInf (mulSupport '' s) := by ext; simp; grind

variable {M'} in
@[to_additive]
theorem IsMulSpanning.comap (hM' : M'.IsMulSpanning) : (M'.comap f).IsMulSpanning := by
  grind [IsMulSpanning, mem_comap]

@[to_additive (attr := simp)]
theorem comap_mulSupport : (M'.comap f).mulSupport = (M'.mulSupport).comap f := by ext; simp

variable {f M} in
@[to_additive]
theorem IsMulSpanning.map (hM : M.IsMulSpanning) (hf : Function.Surjective f) :
    (M.map f).IsMulSpanning := fun x ↦ by
  obtain ⟨x', rfl⟩ := hf x
  grind [IsMulSpanning, mem_map]

end Group

section CommGroup

variable {G H : Type*} [CommGroup G] [CommGroup H] (f : G →* H) (M : Submonoid G)

variable {f M} in
@[to_additive (attr := simp)]
theorem map_mulSupport (hsupp : f.ker ≤ M.mulSupport) :
    (M.map f).mulSupport = (M.mulSupport).map f := by
  ext
  refine ⟨fun ⟨⟨a, ⟨ha₁, ha₂⟩⟩, ⟨b, ⟨hb₁, hb₂⟩⟩⟩ ↦ ?_,
    by grind [Subgroup.mem_map, mem_map, mem_mulSupport]⟩
  have : (a * b)⁻¹ * b ∈ M := mul_mem (hsupp (show f (a * b) = 1 by simp_all)).2 hb₁
  grind [mem_mulSupport, SetLike.mem_coe, mul_inv_rev, inv_mul_cancel_comm, Subgroup.mem_map]

end CommGroup

end Submonoid
-- end #37252

-- begin #37298
variable (G : Type*) [CommGroup G]

@[to_additive]
theorem Submonoid.oneLE.isMulPointed [PartialOrder G] [IsOrderedMonoid G] :
    (oneLE G).IsMulPointed := by simp_all [IsMulPointed, ge_antisymm_iff]

@[to_additive]
theorem Submonoid.oneLE.isMulSpanning [LinearOrder G] [IsOrderedMonoid G] :
    (oneLE G).IsMulSpanning := by simp_all [IsMulSpanning, le_total]

variable {G} {M : Submonoid G} (hM : M.IsMulPointed)

/-- Construct a partial order by designating a submonoid with zero support in an abelian group. -/
@[to_additive
/-- Construct a partial order by designating a submonoid with zero support in an abelian group. -/]
abbrev PartialOrder.mkOfSubmonoid : PartialOrder G where
  le a b := b / a ∈ M
  le_refl a := by simp [one_mem]
  le_trans a b c nab nbc := by simpa using mul_mem nbc nab
  le_antisymm a b nab nba := by
    simpa [div_eq_one, eq_comm] using hM.eq_one_of_mem_of_inv_mem nab (by simpa using nba)

variable {hM} in
@[to_additive (attr := simp)]
theorem PartialOrder.mkOfSubmonoid_le_iff {a b : G} :
    (mkOfSubmonoid hM).le a b ↔ b / a ∈ M := .rfl

@[to_additive]
theorem IsOrderedMonoid.mkOfSubmonoid :
    letI _ := PartialOrder.mkOfSubmonoid hM
    IsOrderedMonoid G :=
  letI _ := PartialOrder.mkOfSubmonoid hM
  { mul_le_mul_left := fun a b nab c ↦ by simpa [· ≤ ·] using nab }

/-- Construct a linear order by designating
    a maximal submonoid with zero support in an abelian group. -/
@[to_additive
/-- Construct a linear order by designating
    a maximal submonoid with zero support in an abelian group. -/]
abbrev LinearOrder.mkOfSubmonoid (hMs : M.IsMulSpanning) [DecidablePred (· ∈ M)] :
    LinearOrder G where
  __ := PartialOrder.mkOfSubmonoid hM
  le_total a b := by simpa using hMs.mem_or_inv_mem (b / a)
  toDecidableLE _ := _
-- end #37298

-- `Mathlib.Algebra.Order.Group.Cone`
namespace CommGroup

variable (G) in
/-- Equivalence between submonoids with zero support in an abelian group `G`
    and partially ordered group structures on `G`. -/
@[to_additive
  /-- Equivalence between submonoids with zero support in an abelian group `G`
    and partially ordered group structures on `G`. -/]
noncomputable def submonoidPartialOrderEquiv :
    Equiv {C : Submonoid G // C.IsMulPointed}
          {o : PartialOrder G // IsOrderedMonoid G} where
  toFun := fun ⟨_, hC⟩ ↦ ⟨.mkOfSubmonoid hC, .mkOfSubmonoid _⟩
  invFun := fun ⟨_, _⟩ ↦ ⟨.oneLE G, Submonoid.oneLE.isMulPointed G⟩
  left_inv := fun ⟨_, _⟩ ↦ by ext; simp
  right_inv := fun ⟨_, _⟩ ↦ by ext; simp [LE.le] -- TODO : figure out why [LE.le] works!

@[to_additive (attr := simp)]
theorem submonoidPartialOrderEquiv_apply
    (C : Submonoid G) (h : C.IsMulPointed) :
    submonoidPartialOrderEquiv G ⟨C, h⟩ = PartialOrder.mkOfSubmonoid h := rfl

@[to_additive (attr := simp)]
theorem submonoidPartialOrderEquiv_symm_apply (o : PartialOrder G) (h : IsOrderedMonoid G) :
    (submonoidPartialOrderEquiv G).symm ⟨o, h⟩ = Submonoid.oneLE G := rfl

open Classical in
variable (G) in
/-- Equivalence between maximal submonoids with zero support in an abelian group `G`
    and linearly ordered group structures on `G`. -/
@[to_additive
  /-- Equivalence between maximal submonoids with zero support in an abelian group `G`
    and linearly ordered group structures on `G`. -/]
noncomputable def submonoidLinearOrderEquiv :
    Equiv {C : Submonoid G // C.IsMulPointed ∧ C.IsMulSpanning}
          {o : LinearOrder G // IsOrderedMonoid G} where
  toFun := fun ⟨C, hC⟩ ↦ ⟨.mkOfSubmonoid hC.1 hC.2, .mkOfSubmonoid hC.1⟩
  invFun := fun ⟨_, _⟩ ↦ ⟨.oneLE G, Submonoid.oneLE.isMulPointed G, Submonoid.oneLE.isMulSpanning G⟩
  left_inv := fun ⟨_, _, _⟩ ↦ by ext; simp
  right_inv := fun ⟨_, _⟩ ↦ by ext; simp

open Classical in
@[to_additive (attr := simp)]
theorem submonoidLinearOrderEquiv_apply
    (C : Submonoid G) (h : C.IsMulPointed ∧ C.IsMulSpanning) :
    submonoidLinearOrderEquiv G ⟨C, h⟩ = LinearOrder.mkOfSubmonoid h.1 h.2 := rfl

@[to_additive (attr := simp)]
theorem submonoidLinearOrderEquiv_symm_apply (l : LinearOrder G) (h : IsOrderedMonoid G) :
    (submonoidLinearOrderEquiv G).symm ⟨l, h⟩ = Submonoid.oneLE G := rfl

end CommGroup

variable {R : Type*} [Ring R]

namespace Subsemiring

variable {S : Subsemiring R}

theorem mem_support {x : R} : x ∈ S.support ↔ x ∈ S ∧ -x ∈ S := by simp

theorem isPointed_def : S.IsPointed ↔ ∀ {x}, x ∈ S → -x ∈ S → x = 0 := by
  simp [AddSubmonoid.IsPointed]

theorem isSpanning_def : S.IsSpanning ↔ ∀ a, a ∈ S ∨ -a ∈ S := by simp [AddSubmonoid.IsSpanning]

theorem _root_.AddSubmonoid.IsPointed.neg_one_notMem [Nontrivial R] (hS : S.IsPointed) :
    -1 ∉ S := fun hc ↦ by
  rw [isPointed_def] at hS
  simpa [hS (one_mem _) hc] using zero_ne_one' R

@[simps!]
def supportIdeal (hS : S.IsSpanning) : Ideal R where
  __ : AddSubgroup R := S.toAddSubmonoid.support
  smul_mem' x a ha := by
    simp_all [isSpanning_def]
    have : ∀ {x y}, -x ∈ S → -y ∈ S → x * y ∈ S := fun hx hy ↦ by simpa using mul_mem hx hy
    grind [mul_mem, neg_mul_mem, mul_neg_mem]

namespace supportIdeal

@[simp] theorem mem_supportIdeal {S : Subsemiring R} (hS : S.IsSpanning) {x : R} :
    x ∈ S.supportIdeal hS ↔ x ∈ S.support := .rfl

@[simp] theorem supportIdeal_toAddSubgroup {S : Subsemiring R} (hS : S.IsSpanning) :
    (S.supportIdeal hS).toAddSubgroup = S.support := rfl

end supportIdeal

-- begin #32889
section upstream

variable {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
         (P : Subsemiring R) (Q : Subsemiring S)

--  existing `comap_toSubmonoid` had RHS in a bad form for `simp` - `Submonoid.mem_mk` doesn't work
@[simp]
theorem comap_toSubmonoid' : (Q.comap f).toSubmonoid = Q.toSubmonoid.comap f.toMonoidHom := by
  ext; simp [-comap_toSubmonoid]

@[simp]
theorem comap_toAddSubmonoid :
    (Q.comap f).toAddSubmonoid = Q.toAddSubmonoid.comap f.toAddMonoidHom := by
  ext; simp

-- existing `map_toSubmonoid` had RHS in a bad form for `simp` - `Submonoid.mem_mk` doesn't work
@[simp]
theorem map_toSubmonoid' : (P.map f).toSubmonoid = P.toSubmonoid.map f.toMonoidHom := by
  ext; simp [-map_toSubmonoid]

@[simp]
theorem map_toAddSubmonoid : (P.map f).toAddSubmonoid = P.toAddSubmonoid.map f.toAddMonoidHom := by
  ext; simp

end upstream
-- end #32889

variable {R R' : Type*} [Ring R] [Ring R'] {f : R →+* R'}
         {S T : Subsemiring R} {S' : Subsemiring R'} {s : Set (Subsemiring R)}

variable (f) in
theorem isSpanning_comap (hS' : S'.IsSpanning) : (S'.comap f).IsSpanning :=
  hS'.comap f.toAddMonoidHom

theorem isSpanning_map (hS : S.IsSpanning) (hf : Function.Surjective f) : (S.map f).IsSpanning :=
  hS.map (f := f.toAddMonoidHom) hf

end Subsemiring

variable (R : Type*) [Ring R]

-- #37298
theorem Subsemiring.nonneg.isPointed [PartialOrder R] [IsOrderedRing R] :
    (Subsemiring.nonneg R).IsPointed := AddSubmonoid.nonneg.isPointed R

-- #37298
theorem Subsemiring.nonneg.isSpanning [LinearOrder R] [IsOrderedRing R] :
    (Subsemiring.nonneg R).IsSpanning := AddSubmonoid.nonneg.isSpanning R

variable {R} {S : Subsemiring R} (hS : S.IsPointed)

-- #37298
theorem IsOrderedRing.mkOfSubsemiring :
    letI _ := PartialOrder.mkOfAddSubmonoid hS
    IsOrderedRing R :=
  letI _ := PartialOrder.mkOfAddSubmonoid hS
  haveI := IsOrderedAddMonoid.mkOfAddSubmonoid hS
  haveI : ZeroLEOneClass R := ⟨by simp⟩
  .of_mul_nonneg fun x y xnn ynn ↦ show _ ∈ S by simpa using Subsemiring.mul_mem _ xnn ynn

-- `Mathlib.Algebra.Order.Ring.Cone`
namespace Ring

variable (R) in
/-- Equivalence between subsemirings with zero support in a ring `R`
    and partially ordered ring structures on `R`. -/
noncomputable def isPointedPartialOrderEquiv :
    Equiv {C : Subsemiring R // C.IsPointed}
          {o : PartialOrder R // IsOrderedRing R} where
  toFun := fun ⟨_, hC⟩ ↦ ⟨.mkOfAddSubmonoid hC, .mkOfSubsemiring _⟩
  invFun := fun ⟨_, _⟩ ↦ ⟨.nonneg R, Subsemiring.nonneg.isPointed R⟩
  left_inv := fun ⟨_, _⟩ ↦ by ext; simp
  right_inv := fun ⟨_, _⟩ ↦ by ext; simp [LE.le]

@[simp]
theorem isPointedPartialOrderEquiv_apply
    (C : Subsemiring R) (h : C.IsPointed) :
    isPointedPartialOrderEquiv R ⟨C, h⟩ = PartialOrder.mkOfAddSubmonoid h := rfl

@[simp]
theorem isPointedPartialOrderEquiv_symm_apply (o : PartialOrder R) (h : IsOrderedRing R) :
    (isPointedPartialOrderEquiv R).symm ⟨o, h⟩ = Subsemiring.nonneg R := rfl

variable (R) in
open Classical in
/-- Equivalence between maximal subsemirings with zero support in a ring `R`
    and linearly ordered ring structures on `R`. -/
noncomputable def isPointedLinearOrderEquiv :
    Equiv {C : Subsemiring R // C.IsPointed ∧ C.IsSpanning}
          {o : LinearOrder R // IsOrderedRing R} where
  toFun := fun ⟨C, hC⟩ ↦ ⟨.mkOfAddSubmonoid hC.1 hC.2, .mkOfSubsemiring hC.1⟩
  invFun := fun ⟨_, _⟩ ↦
    ⟨.nonneg R, Subsemiring.nonneg.isPointed R, Subsemiring.nonneg.isSpanning R⟩
  left_inv := fun ⟨_, _, _⟩ ↦ by ext; simp
  right_inv := fun ⟨_, _⟩ ↦ by ext; simp

open Classical in
@[simp]
theorem isPointedLinearOrderEquiv_apply
    (C : Subsemiring R) (h : C.IsPointed ∧ C.IsSpanning) :
    isPointedLinearOrderEquiv R ⟨C, h⟩ = LinearOrder.mkOfAddSubmonoid h.1 h.2 := rfl

@[simp]
theorem isPointedLinearOrderEquiv_symm_apply (o : LinearOrder R) (h : IsOrderedRing R) :
    (isPointedLinearOrderEquiv R).symm ⟨o, h⟩ = Subsemiring.nonneg R := rfl

end Ring

/- TODO : quotient versions: need to lift the constructions to prop equality?

theorem Quotient.image_mk_eq_lift {α : Type*} {s : Setoid α} (A : Set α)
    (h : ∀ x y, x ≈ y → (x ∈ A ↔ y ∈ A)) :
    (Quotient.mk s) '' A = (Quotient.lift (· ∈ A) (by simpa)) := by
  aesop (add unsafe forward Quotient.exists_rep)

@[to_additive]
theorem QuotientGroup.mem_iff_mem_of_rel {G S : Type*} [CommGroup G]
    [SetLike S G] [MulMemClass S G] (H : Subgroup G) {M : S} (hM : (H : Set G) ⊆ M) :
    ∀ x y, QuotientGroup.leftRel H x y → (x ∈ M ↔ y ∈ M) := fun x y hxy ↦ by
  rw [QuotientGroup.leftRel_apply] at hxy
  exact ⟨fun h ↦ by simpa using mul_mem h <| hM hxy,
        fun h ↦ by simpa using mul_mem h <| hM <| inv_mem hxy⟩

def decidablePred_mem_map_quotient_mk
    {R S : Type*} [CommRing R] [SetLike S R] [AddMemClass S R] (I : Ideal R)
    {M : S} (hM : (I : Set R) ⊆ M) [DecidablePred (· ∈ M)] :
    DecidablePred (· ∈ (Ideal.Quotient.mk I) '' M) := by
  have : ∀ x y, I.quotientRel x y → (x ∈ M ↔ y ∈ M) :=
    QuotientAddGroup.mem_iff_mem_of_rel _ (by simpa)
  rw [show (· ∈ (Ideal.Quotient.mk I) '' _) = (· ∈ (Quotient.mk _) '' _) by rfl,
      Quotient.image_mk_eq_lift _ this]
  exact Quotient.lift.decidablePred (· ∈ M) (by simpa)

-- end upstream

section Quot

-- TODO : group and partial versions

variable {R : Type*} [CommRing R] (O : Subsemiring R) (hO : O.IsSpanning)

instance : (O.map (Ideal.Quotient.mk O.support)).IsSpanning :=
  AddSubmonoid.IsSpanning.map O.toAddSubmonoid
    (f := (Ideal.Quotient.mk O.support).toAddMonoidHom) Ideal.Quotient.mk_surjective

-- TODO : move to right place
@[simp]
theorem RingHom.ker_toAddSubgroup {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
  (RingHom.ker f).toAddSubgroup = f.toAddMonoidHom.ker := by ext; simp

-- TODO : make proof less awful
instance : (O.map (Ideal.Quotient.mk O.support)).IsPointed where
  supportAddSubgroup_eq_bot := by
    have : (O.toAddSubmonoid.map (Ideal.Quotient.mk O.support).toAddMonoidHom).HasIdealSupport := by
      simpa using inferInstanceAs (O.map (Ideal.Quotient.mk O.support)).HasIdealSupport
    have fact : (Ideal.Quotient.mk O.support).toAddMonoidHom.ker = O.supportAddSubgroup := by
      have := Ideal.mk_ker (I := O.support)
      apply_fun Submodule.toAddSubgroup at this
      simpa [-Ideal.mk_ker, -RingHom.toAddMonoidHom_eq_coe]
    have : (Ideal.Quotient.mk O.support).toAddMonoidHom.ker ≤ O.supportAddSubgroup := by
      simp [-RingHom.toAddMonoidHom_eq_coe, fact]
    have := AddSubmonoid.map_support Ideal.Quotient.mk_surjective this
    simp [-RingHom.toAddMonoidHom_eq_coe, this]

abbrev PartialOrder.mkOfSubsemiring_quot : PartialOrder (R ⧸ O.support) :=
  .mkOfAddSubmonoid (O.map (Ideal.Quotient.mk O.support)).toAddSubmonoid

theorem IsOrderedRing.mkOfSubsemiring_quot :
    letI  _ := PartialOrder.mkOfSubsemiring_quot O
    IsOrderedRing (R ⧸ O.support) := .mkOfSubsemiring (O.map (Ideal.Quotient.mk O.support))

abbrev LinearOrder.mkOfSubsemiring_quot [DecidablePred (· ∈ O)] : LinearOrder (R ⧸ O.support) :=
  have : DecidablePred (· ∈ O.map (Ideal.Quotient.mk O.support)) := by
    simpa using decidablePred_mem_map_quotient_mk (O.support)
      (by simp [AddSubmonoid.coe_support])
  .mkOfAddSubmonoid (O.map (Ideal.Quotient.mk O.support)).toAddSubmonoid

-- TODO : come up with correct statement and name
open Classical in
noncomputable def subsemiringLinearOrderEquiv (I : Ideal R) :
    Equiv {O : Subsemiring R // ∃ _ : O.IsSpanning, O.support = I}
          {o : LinearOrder (R ⧸ I) // IsOrderedRing (R ⧸ I)} where
  toFun := fun ⟨O, hO⟩ ↦ have := hO.1; have hs := hO.2; ⟨by rw [← hs]; exact .mkOfSubsemiring_quot O, .mkOfSubsemiring_quot O⟩
  invFun := fun ⟨o, ho⟩ ↦
    ⟨((Ring.isPointedLinearOrderEquiv _).symm ⟨o, ho⟩).val.comap (Ideal.Quotient.mk I),
    ⟨fun a ↦ by simpa using le_total ..⟩⟩
  left_inv := fun ⟨O, hO⟩ ↦ by
    ext x
    simp [-Subsemiring.mem_map]
    constructor
    · simp
      intro y hy hxy
      rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, Ideal.mk_ker] at hxy
      simpa using add_mem hxy.2 hy
    · aesop
  right_inv := fun ⟨I, l, hl⟩ ↦ by
    refine Sigma.eq ?_ ?_
    · ext; simp [AddSubmonoid.mem_support, ← ge_antisymm_iff, ← RingHom.mem_ker]
    · simp
      apply Subtype.ext
      simp
      sorry -- TODO : fix DTT hell

/- TODO : apply and symm_apply simp lemmas -/

end Quot

-/
