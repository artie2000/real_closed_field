import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic

import RealClosedField
import RealClosedField.Algebra.Order.Field.IsSemireal

open Set Polynomial Filter Classical

noncomputable section

variable {R : Type*}
variable [Field R] [IsRealClosed R]

instance : LinearOrder R := LinearOrder.ofIsSemireal R

lemma or_neg_of_mul_neg (a b : R) : a * b < 0 → a < 0 ∨ b < 0 := by
  intro h
  apply or_iff_not_imp_left.mpr
  intro ha
  nlinarith

def rootsInInterval (f : Polynomial R) (a b : R) : Finset R :=
  f.roots.toFinset.filter (fun x => x ∈ Ioo a b)

def sgn (k : R) : ℤ  :=
  if k > 0 then 1
  else if k = 0 then 0
  else -1

lemma sgn_sgn_neg : ∀ x : R, sgn x < 0 ↔ x < 0 := by
  intro x
  unfold sgn
  split_ifs
  next h =>
    simp only [Int.reduceLT, false_iff, not_lt]
    exact le_of_lt h
  next h1 h2 => simp [h2]
  next h1 h2 =>
    simp only [Int.reduceNeg, Left.neg_neg_iff, zero_lt_one, true_iff]
    push_neg at h1 h2
    exact lt_of_le_of_ne h1 h2

lemma sgn_sgn_zero : ∀ x : R, sgn x = 0 ↔ x = 0 := by
  intro x
  unfold sgn
  split_ifs
  next h => simp only [one_ne_zero, false_iff]; exact ne_of_gt h
  next h => simp [h]
  next h1 h2 => simp [h2]

lemma sgn_sgn_pos : ∀ x : R, sgn x > 0 ↔ x > 0 := by
  intro x
  unfold sgn
  split_ifs
  next h => simp [h]
  next h1 h2 => simp [h2]
  next h1 h2 => simp [h1]

def sgn_pos_inf (p : Polynomial R) : ℤ :=
  sgn p.leadingCoeff

def sgn_neg_inf (p : Polynomial R) : ℤ :=
  if Even p.natDegree then sgn p.leadingCoeff else - sgn p.leadingCoeff

-- TODO (Tomaz): Add simp annotations to all these and fix everything that breaks
-- NOTE (Tomaz): I think only `sturmSeq` cannot be annotated with simp
def seq_sgn_pos_inf : List (Polynomial R) → List R
| [] => []
| p::ps => sgn_pos_inf p :: seq_sgn_pos_inf ps

def seq_sgn_neg_inf : List (Polynomial R) → List R
| [] => []
| p::ps => sgn_neg_inf p :: seq_sgn_neg_inf ps

def tarskiQuery (f g : Polynomial R) (a b : R) : ℤ :=
  ∑ x ∈ rootsInInterval f a b, sgn (g.eval x)

lemma rootsInIntervalZero (a b : R) : rootsInInterval 0 a b = ∅ := by simp [rootsInInterval]

@[simp]
def rootsInSet (p : Polynomial R) (S : Set R) : Finset R :=
  p.roots.toFinset.filter (fun x => x ∈ S)

lemma rootsInSet_interval (p : Polynomial R) (a b : R) :
    rootsInInterval p a b = rootsInSet p (Set.Ioo a b) := by simp [rootsInInterval]

lemma rootsInSet_cup (p : Polynomial R) (S T : Set R) :
    rootsInSet p S ∪ rootsInSet p T = rootsInSet p (S ∪ T) := by
  simp only [rootsInSet, mem_union]
  exact Finset.filter_union_right (fun x => x ∈ S) (fun x => x ∈ T) p.roots.toFinset

lemma sgn_inf_comp (p : Polynomial R) :
    sgn_neg_inf p = sgn_pos_inf (p.comp (-Polynomial.X)) := by
  by_cases Even p.natDegree
  next H =>
    simp [sgn_neg_inf, sgn_pos_inf, H]
  next H =>
    simp [sgn_neg_inf, sgn_pos_inf, H, sgn]
    simp_all only [Nat.not_even_iff_odd, Odd.neg_one_pow, neg_mul, one_mul, Int.reduceNeg, Left.neg_pos_iff]
    split_ifs
    · linarith
    · simp_all only [natDegree_zero, Nat.not_odd_zero]
    · rfl
    · simp_all only [natDegree_zero, Nat.not_odd_zero]
    · rfl
    · rfl
    · simp_all only [not_lt, neg_neg]
      have : 0 = p.leadingCoeff := by linarith
      have : p = 0 := leadingCoeff_eq_zero.mp (Eq.symm this)
      contradiction

lemma next_non_root_interval (p : Polynomial R) (lb : R) (hp : p ≠ 0) :
    ∃ ub : R, lb < ub ∧ (∀ z ∈ Ioc lb ub, eval z p ≠ 0) := by
  by_cases ∃ r : R, eval r p = 0 ∧ r > lb
  next hr =>
    obtain ⟨r, hr1, hr2⟩ := hr
    let S := p.roots.toFinset.filter (fun w => w > lb)
    if hS: Finset.Nonempty S then
      obtain ⟨lr, hlr⟩ := Finset.min_of_nonempty hS
      have : lr ∈ S := Finset.mem_of_min hlr
      simp [S] at this
      have H2 : ∀ z ∈ Ioo lb lr, eval z p ≠ 0 := by
        intros z hz
        simp at hz
        obtain ⟨hz1, hz2⟩ := hz
        intro abs
        have : z ∉ S := Finset.notMem_of_lt_min hz2 hlr
        simp [S] at this
        have := this hp abs
        linarith
      use (lb + lr) / 2
      simp
      constructor
      · linarith
      · intros z hz1 hz2 abs
        have : z ∈ Ioo lb lr := by
          simp
          constructor
          · exact hz1
          · linarith
        have := H2 z this
        exact this abs
    else
      use lb + 1
      simp only [lt_add_iff_pos_right, zero_lt_one, mem_Ioc, ne_eq, and_imp, true_and]
      intros z hz1 hz2 abs
      have : z ∈ S := by simp [S, hp, abs, hz1]
      have : Finset.Nonempty S := by simp_all only [ne_eq, gt_iff_lt,
        Finset.not_nonempty_iff_eq_empty, Finset.notMem_empty]
      exact hS this
  next hr =>
    push_neg at hr
    use lb + 1
    simp only [lt_add_iff_pos_right, zero_lt_one, mem_Ioc, ne_eq, and_imp, true_and]
    intros z hz1 hz2 abs
    have := hr z abs
    linarith

lemma last_non_root_interval (p : Polynomial R) (ub : R) (hp : p ≠ 0) :
    ∃ lb : R, lb < ub ∧ (∀ z ∈ Ico lb ub, eval z p ≠ 0) := by
  by_cases ∃ r : R, eval r p = 0 ∧ r < ub
  next hr =>
    obtain ⟨r, hr1, hr2⟩ := hr
    let S := p.roots.toFinset.filter (fun w => w < ub)
    if hS: Finset.Nonempty S then
      obtain ⟨mr, hmr⟩ := Finset.max_of_nonempty hS
      have : mr ∈ S := Finset.mem_of_max hmr
      simp [S] at this
      have H2 : ∀ z ∈ Ioo mr ub, eval z p ≠ 0 := by
        intros z hz
        simp at hz
        obtain ⟨hz1, hz2⟩ := hz
        intro abs
        have : z ∉ S := Finset.notMem_of_max_lt hz1 hmr
        simp [S] at this
        have := this hp abs
        linarith
      use (mr + ub) / 2
      simp
      constructor
      · linarith
      · intros z hz1 hz2 abs
        have : z ∈ Ioo mr ub := by
          simp
          constructor
          · linarith
          · exact hz2
        have := H2 z this
        exact this abs
    else
      use ub - 1
      simp
      intros z hz1 hz2 abs
      have : z ∈ S := by simp [S, abs, hz2, hp]
      have : Finset.Nonempty S := by simp_all only [ne_eq, Finset.not_nonempty_iff_eq_empty,
        Finset.notMem_empty]
      exact hS this
  next hr =>
    push_neg at hr
    use ub - 1
    simp
    intros z hz1 hz2 abs
    have := hr z abs
    linarith

theorem intermediate_value_property' : ∀ p: Polynomial R, ∀ (a b : R), a <= b → eval a p <= 0 → 0 <= eval b p -> ∃ r: R, r >= a ∧ r <= b ∧ eval r p = 0 := by
  intros p a b hab ha hb
  have h1 : eval a (-p) ≥ 0 := by
    simp [ha]
  have h2 : eval b (-p) ≤ 0 := by
    simp [hb]
  obtain ⟨r, hr1, hr2⟩  := IsRealClosed.intermediate_value_property (f := -p) hab h1 h2
  simp only [mem_Icc] at hr1
  simp only [eval_neg, neg_eq_zero] at hr2
  use r
  simp_all only [eval_neg, ge_iff_le, Left.nonneg_neg_iff, Left.neg_nonpos_iff, and_self]

theorem intermediate_value_property'_ioo {p: Polynomial R} {a b : R} (hab: a <= b) (hap: eval a p < 0) (hbp: eval b p > 0): ∃ r: R, r > a ∧ r < b ∧ eval r p = 0 := by
  obtain ⟨r, hr1, hr2, hr3⟩ := intermediate_value_property' p a b hab (le_of_lt hap) (le_of_lt hbp)
  have : ¬ r = a := by
    intro abs
    rw [<- abs] at hap
    linarith
  have : r > a := Std.lt_of_le_of_ne hr1 fun a_1 ↦ this (Eq.symm a_1)
  have : ¬ r = b := by
    intro abs
    rw [<- abs] at hbp
    linarith
  have : r < b := Std.lt_of_le_of_ne hr2 this
  use r

theorem intermediate_value_property_ioo {p: Polynomial R} {a b : R} (hab: a <= b) (hap: eval a p > 0) (hbp: eval b p < 0): ∃ r: R, r > a ∧ r < b ∧ eval r p = 0 := by
  obtain ⟨r, hr1, hr3⟩ := IsRealClosed.intermediate_value_property (f := p) hab (le_of_lt hap) (le_of_lt hbp)
  simp at hr1
  obtain ⟨hr1, hr2⟩ := hr1
  have : ¬ r = a := by
    intro abs
    rw [<- abs] at hap
    linarith
  have : r > a := Std.lt_of_le_of_ne hr1 fun a_1 ↦ this (Eq.symm a_1)
  have : ¬ r = b := by
    intro abs
    rw [<- abs] at hbp
    linarith
  have : r < b := Std.lt_of_le_of_ne hr2 this
  use r

theorem exists_root_ioo_mul {p: Polynomial R} {a b: R} (hab: a ≤ b) (hap: (eval a p) * (eval b p) < 0) : ∃ r: R, r > a ∧ r < b ∧ eval r p = 0 := by
  if H: eval a p > 0 then
    have haux: eval b p < 0 := by nlinarith
    exact intermediate_value_property_ioo hab H haux
  else
    have haux1: eval b p > 0 := by nlinarith
    have haux: eval a p < 0 := by nlinarith
    exact intermediate_value_property'_ioo hab haux haux1

lemma not_eq_pos_or_neg_iff_1 (p : Polynomial R) (lb ub : R) :
    (∀ z ∈ Ioc lb ub, eval z p ≠ 0) ↔ ((∀ z ∈ Ioc lb ub, eval z p < 0) ∨ (∀ z ∈ Ioc lb ub, 0 < eval z p)) := by
  by_contra!
  cases this
  next H =>
    obtain ⟨H₁, ⟨z₁, hz₁, hz₁'⟩, ⟨z₂, hz₂, hz₂'⟩⟩ := H
    have z1Neq0 : eval z₁ p ≠ 0 := by aesop
    have z1Pos : 0 < eval z₁ p := lt_of_le_of_ne hz₁' (id (Ne.symm z1Neq0))
    have z2Neg : eval z₂ p < 0 := lt_of_le_of_ne hz₂' (H₁ z₂ hz₂)
    by_cases z₁ < z₂
    next hle =>
      obtain ⟨r, hr₁, hr₂, hr₃⟩ := intermediate_value_property' (-p) z₁ z₂ (le_of_lt hle) (by simp; exact hz₁') (by simp; exact hz₂')
      simp at hr₃
      have : r ∈ Set.Ioc lb ub := by
        simp at hz₁ hz₂ ⊢
        constructor <;> linarith
      exact H₁ r this hr₃
    next hge =>
      push_neg at hge
      obtain ⟨r, hr₁, hr₂, hr₃⟩ := intermediate_value_property' p z₂ z₁ hge (le_of_lt z2Neg) (le_of_lt z1Pos)
      have : r ∈ Set.Ioc lb ub := by
        simp at hz₁ hz₂ ⊢
        constructor
        · linarith
        · linarith
      exact H₁ r this hr₃
  next H =>
    obtain ⟨⟨z, hz1, hz2⟩, H₂⟩ := H
    cases H₂
    next H₂ =>
      have := H₂ z hz1
      linarith
    next H₂ =>
      have := H₂ z hz1
      linarith

lemma derivative_ne_0 (p : Polynomial R) (x : R) (hev : eval x p = 0) (hp : p ≠ 0) : derivative p ≠ 0 := by
  intro abs
  have := natDegree_eq_zero_of_derivative_eq_zero abs
  obtain ⟨c, hc⟩  := (natDegree_eq_zero.mp this)
  have : c ≠ 0 := by
    intro abs2
    rw [abs2] at hc
    rw [<- hc] at hp
    simp at hp
  rw [<- hc] at hev
  simp at hev
  exact this hev

theorem hc : ∀ {a b t : R} , ∀ {P : R[X]},
    a ≤ b → t ∈ Set.Ioo (P.eval a) (P.eval b) → ∃ s, s ∈ Set.Ioo a b ∧ P.eval s = t := by
  intros a b t P hab ht
  let Q := P - C t
  simp at ht
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨r, hr1, hr2, hr3⟩ := intermediate_value_property'_ioo (p := Q) hab (by simp [Q, ht1]) (by simp [Q, ht2])
  use r
  constructor
  · simp [hr1, hr2]
  · simp [Q] at hr3
    grind

lemma polynomial_has_root_of_le_zero_of_pos {a b : R} (hab : a ≤ b)
    {P : R[X]} (ha : P.eval a < 0) (hb : 0 < P.eval b ) : ∃ s ∈ Ioo a b , P.eval s = 0 := by
  exact hc hab ⟨ha, hb⟩

lemma polynomial_has_root_of_pos_le_zero {a b : R} (hab : a ≤ b)
    {P : R[X]} (ha : 0 < P.eval a) (hb : P.eval b < 0 ) : ∃ s ∈ Ioo a b , P.eval s = 0 := by
  obtain ⟨s, hs1, hs2⟩ := @hc R _ _ a b 0 (- P) hab (by simp[ha, hb])
  simp only [eval_neg, neg_eq_zero] at hs2
  exact ⟨s, hs1, hs2 ⟩

lemma polynomial_has_root_of_mul_neg {a b : R} (hab : a ≤ b)
    {P : R[X]} (habm : (P.eval a) * (P.eval b) < 0) : ∃ s ∈ Ioo a b , P.eval s = 0 := by
  rcases lt_trichotomy (P.eval a) 0 with hl1 | hl2 | hl3
  · have : eval b P > 0 := by nlinarith
    exact polynomial_has_root_of_le_zero_of_pos hab hl1 this
  · simp[hl2] at habm
  · have : eval b P < 0 := by nlinarith
    exact polynomial_has_root_of_pos_le_zero hab hl3 this

lemma neg_of_ne_zero_of_exists_neg  {a b m : R} {P : R[X]}
    (hP : ∀ x ∈ Ioo a b , P.eval x ≠ 0) (hm : m ∈ Ioo a b) (hneg : P.eval m < 0) :
    ∀ x ∈ Ioo a b , P.eval x < 0 := by
  intro x hx
  by_contra! hc'
  rcases le_iff_lt_or_eq.1 hc' with hz1 | hz2
  · rcases le_or_gt m x with hm1 | hm2
    · obtain ⟨s, hs1, hs2⟩ := polynomial_has_root_of_le_zero_of_pos hm1 hneg hz1
      refine hP s ?_ hs2
      simp only [mem_Ioo] at hs1 hx ⊢
      exact ⟨lt_trans hm.1 hs1.1, lt_trans hs1.2 hx.2⟩
    · obtain ⟨s, hs1, hs2⟩ := polynomial_has_root_of_pos_le_zero (le_of_lt hm2) hz1 hneg
      refine hP s ?_ hs2
      simp only [mem_Ioo] at hs1 hx ⊢
      exact ⟨lt_trans hx.1 hs1.1, lt_trans hs1.2 hm.2⟩
  · exact hP x hx hz2.symm

lemma pos_of_ne_zero_of_exists_pos  {a b m : R} {P : R[X]}
    (hP : ∀ x ∈ Ioo a b , P.eval x ≠ 0) (hm : m ∈ Ioo a b) (hpos : P.eval m > 0) :
    ∀ x ∈ Ioo a b , P.eval x > 0 := by
  have := neg_of_ne_zero_of_exists_neg (P := - P)
    (by simp only [eval_neg, ne_eq, neg_eq_zero] ; exact hP ) hm (by simp[hpos])
  simp at this ⊢
  exact this

lemma constant_sign_of_ne_zero  {a b : R} (hab : a ≤ b)
    {P : R[X]} (hP : ∀ x ∈ Ioo a b, P.eval x ≠ 0) :
    (∀ x ∈ Ioo a b , P.eval x > 0) ∨ (∀ x ∈ Ioo a b , P.eval x < 0)  := by
  rcases le_iff_lt_or_eq.1 hab with h1 | h2
  · obtain ⟨m, hm⟩ := exists_between  h1
    rcases lt_trichotomy (P.eval m) 0 with hl1 | hl2 | hl3
    · right
      exact neg_of_ne_zero_of_exists_neg hP hm hl1
    · exfalso ; exact hP m hm hl2
    · left
      exact pos_of_ne_zero_of_exists_pos hP hm hl3
  · simp [h2]

lemma nonpos_of_ne_zero_of_exists_neg  {a b m : R} {P : R[X]}
    (hP : ∀ x ∈ Ioo a b , P.eval x ≠ 0) (hm : m ∈ Ioo a b) (hneg : P.eval m < 0) :
    ∀ x ∈ Icc a b , P.eval x ≤ 0 := by
  intro x hmem
  rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc hmem with ha | hb | hx
  · rw [ha]
    by_contra! hc'
    obtain ⟨s, hs1, hs2⟩ := polynomial_has_root_of_pos_le_zero (le_of_lt hm.1) hc' hneg
    refine hP s ?_ hs2
    simp only [mem_Ioo] at hs1
    exact ⟨hs1.1, lt_trans hs1.2 hm.2⟩
  · rw [hb]
    by_contra! hc'
    obtain ⟨s, hs1, hs2⟩ := polynomial_has_root_of_le_zero_of_pos (le_of_lt hm.2) hneg hc'
    refine hP s ?_ hs2
    simp only [mem_Ioo] at hs1
    exact ⟨lt_trans hm.1 hs1.1, hs1.2⟩
  · exact le_of_lt (neg_of_ne_zero_of_exists_neg hP hm hneg x hx)

lemma nonneg_of_ne_zero_of_exists_pos {a b m : R} {P : R[X]}
    (hP : ∀ x ∈ Ioo a b , P.eval x ≠ 0) (hm : m ∈ Ioo a b) (hpos : P.eval m > 0) :
    ∀ x ∈ Icc a b , P.eval x ≥ 0 := by
  have := nonpos_of_ne_zero_of_exists_neg (P := - P)
    (by simp only [eval_neg, ne_eq, neg_eq_zero] ; exact hP ) hm (by simp[hpos])
  simp at this ⊢
  exact this

lemma constant_sign_of_ne_zero' {a b : R} (hab : a ≤ b)
    {P : R[X]} (hP : ∀ x ∈ Ioo a b, P.eval x ≠ 0) :
    (∀ x ∈ Icc a b , P.eval x ≥ 0) ∨ (∀ x ∈ Icc a b , P.eval x ≤ 0) := by
  rcases le_iff_lt_or_eq.1 hab with h1 | h2
  · obtain ⟨m, hm⟩ := exists_between  h1
    rcases lt_trichotomy (P.eval m) 0 with hl1 | hl2 | hl3
    · right
      exact nonpos_of_ne_zero_of_exists_neg hP hm hl1
    · exfalso ; exact hP m hm hl2
    · left
      exact nonneg_of_ne_zero_of_exists_pos hP hm hl3
  · simp [h2, LinearOrder.le_total 0 (eval b P)]

lemma rolle_theorem_weak {a b : R} (hab : a < b) {P : R[X]}
    (hP : ∀ x ∈ Ioo a b, P.eval x ≠ 0) (hPa : P.eval a = 0) (hPb : P.eval b = 0) :
    ∃ c ∈ Ioo a b , (derivative P).eval c = 0 := by
  have hPnz : P ≠ 0 := by
    intro h
    obtain ⟨m, hm⟩ := exists_between hab
    specialize hP m hm
    simp [h, eval_zero] at hP
  obtain ⟨Q' , hQ'1, hQ'2⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hPnz a
  have hQnz : Q' ≠ 0 := by
    intro h
    rw [h, mul_zero] at hQ'1
    exact hPnz hQ'1
  obtain ⟨Q , hQ1, hQ2⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q' hQnz b
  rw [hQ1] at hQ'1
  have ham : rootMultiplicity a P ≠ 0 := by
    rw [← pos_iff_ne_zero]
    refine (Polynomial.rootMultiplicity_pos hPnz).2 ?_
    exact hPa
  have hbm : rootMultiplicity b Q' ≠ 0 := by
    rw [← pos_iff_ne_zero]
    refine (Polynomial.rootMultiplicity_pos hQnz).2 ?_
    rw [hQ'1 ] at hPb
    simp[(sub_ne_zero_of_ne (Ne.symm (ne_of_lt hab))), hQnz] at hPb
    rcases hPb with hPb1 | hPb2
    · exact hPb1
    · rw [hQ1]
      simp[hPb2]
  rw [← Nat.succ_pred_eq_of_ne_zero ham, ← Nat.succ_pred_eq_of_ne_zero hbm] at hQ'1
  have hQr : Q.eval a ≠ 0 ∧ Q.eval b ≠ 0 := by
    constructor
    · intro hc
      apply hQ'2
      rw [Polynomial.dvd_iff_isRoot, hQ1]
      simp[hc]
    · rwa [Polynomial.dvd_iff_isRoot] at hQ2
  set Q1 : R[X] := C (rootMultiplicity b Q' : R) * (X - C a) * Q +
      C (rootMultiplicity a P : R) * (X - C b) * Q + (X - C a) * (X - C b) * derivative Q with hQd
  have hderiv : derivative P = ((X - C a) ^ (rootMultiplicity a P).pred) *
    ((X - C b) ^ (rootMultiplicity b Q').pred) * Q1 := by
    nth_rw 1 [hQ'1, hQd, ← mul_assoc, derivative_mul, derivative_mul,
      derivative_pow, derivative_pow, derivative_X_sub_C, derivative_X_sub_C, mul_one, mul_one]
    rw [mul_add, mul_add, add_mul _ _ Q]
    nth_rw 2 [add_comm]
    have : ∀ n : ℕ , (n : R[X]) + 1 = ↑(n + 1) := fun n => by simp only [Nat.cast_add, Nat.cast_one]
    congr 1
    congr 1
    · simp [Nat.succ_eq_add_one] ; simp_rw [this, Nat.sub_one_add_one hbm] ; ring
    · simp [Nat.succ_eq_add_one] ; simp_rw [this, Nat.sub_one_add_one ham] ; ring
    · simp [Nat.succ_eq_add_one] ; ring
  have hQ1a : Q1.eval a =  - (rootMultiplicity a P) * (b - a) * (Q.eval a) := by
    rw [hQd] ; simp ; ring
  have hQ1b : Q1.eval b =  (rootMultiplicity b Q') * (b - a) * (Q.eval b) := by
    rw [hQd] ; simp
  have hQIoo : ∀ x ∈ Ioo a b, Q.eval x ≠ 0 := by
    intro x hmem h
    apply hP x hmem
    rw [hQ'1] ; simp[h]
  have hzQ : ∃ c ∈ Ioo a b , Q1.eval c = 0 := by
    apply polynomial_has_root_of_mul_neg (le_of_lt hab)
    simp [hQ1a, hQ1b]
    have : ↑(rootMultiplicity a P) * (b - a) * eval a Q * (↑(rootMultiplicity b Q') * (b - a) * eval b Q) =
      ↑(rootMultiplicity a P) * (↑(rootMultiplicity b Q') * (b - a) * (b - a) * ((eval a Q) * (eval b Q))) := by ring
    rw [this]
    refine mul_pos ?_ (mul_pos ((mul_pos ((mul_pos ?_ ?_)) ?_)) ?_)
    · rw [Nat.cast_pos]
      exact Nat.pos_of_ne_zero ham
    · rw [Nat.cast_pos]
      exact Nat.pos_of_ne_zero hbm
    · linarith
    · linarith
    · refine lt_of_le_of_ne ?_ ?_
      · rcases constant_sign_of_ne_zero' (le_of_lt hab) hQIoo with hqal | hqag
        · refine mul_nonneg (hqal a (by simp [le_of_lt hab])) (hqal b (by simp [le_of_lt hab]))
        · refine mul_nonneg_of_nonpos_of_nonpos (hqag a (by simp [le_of_lt hab]))
            (hqag b (by simp [le_of_lt hab]))
      · simp[hQr]
  obtain ⟨c, hcI, hc⟩ := hzQ
  use c
  refine ⟨hcI, ?_ ⟩
  simp [hderiv, hc]

lemma rolle_theorem_weak' {a b : R} (hab : a < b) {P : R[X]}
    (hPa : P.eval a = 0) (hPb : P.eval b = 0) :
    ∃ c ∈ Ioo a b , ((derivative P).eval c = 0 ∨ P.eval c = 0) := by
  by_contra! hcc
  have hP : ∀ x ∈ Ioo a b , P.eval x ≠ 0 := fun x hx => (hcc x hx).2
  obtain ⟨c, hc1, hc2⟩ := rolle_theorem_weak hab hP hPa hPb
  exact (hcc c hc1).1 hc2

open Finset

lemma rolle_theorem_induction (n : ℕ)
    {a b : R} {P : R[X]} (hab : a < b) (hPa : P.eval a = 0) (hPb : P.eval b = 0)
    (hcard : #((Multiset.toFinset P.roots).filter ( fun x => x ∈ Ioo a b)) < n) :
    ∃ c ∈ Ioo a b, (derivative P).eval c = 0 := by
  revert P a b
  induction' n with n hn
  · simp only [Set.mem_Ioo, not_lt_zero', IsEmpty.forall_iff, implies_true]
  · intro a b P hab hPa hPb hcard
    obtain ⟨c , hcmem, hcd⟩ := rolle_theorem_weak' hab hPa hPb
    rcases hcd with hcd1 | hcd2
    · exact ⟨c, hcmem, hcd1⟩
    · have : P ≠ 0 → filter (fun x ↦ x ∈ Set.Ioo a c) P.roots.toFinset
        ⊂ filter (fun x ↦ x ∈ Set.Ioo a b) P.roots.toFinset := by
        intro hPz
        rw [Finset.ssubset_def, Finset.not_subset]
        constructor
        · intro r hr
          simp at hr ⊢
          refine ⟨hr.1, ⟨hr.2.1, lt_trans hr.2.2 hcmem.2 ⟩ ⟩
        · use c
          simp [hcd2, hPz]
          exact hcmem
      by_cases hPz : P = 0
      · simp [hPz, exists_between hab]
      · obtain ⟨r, hr1, hr2⟩ := hn hcmem.1 hPa hcd2 (by linarith [Finset.card_lt_card (this hPz)])
        refine ⟨r, ⟨hr1.1, lt_trans hr1.2 hcmem.2⟩, hr2  ⟩

theorem rolle_theorem  {a b : R} {P : R[X]} (hab : a < b)
    (hPab : P.eval a = P.eval b) : ∃ c ∈ Ioo a b, (derivative P).eval c = 0 := by
  wlog h : P.eval a = 0
  · have := this (P := P - C (P.eval a) ) hab
    simp at this
    simp [this, hPab]
  · rw [h] at hPab
    exact rolle_theorem_induction
      ((#((Multiset.toFinset P.roots).filter ( fun x => x ∈ Ioo a b))) + 1)
      hab h hPab.symm (lt_add_one _)

theorem mean_value_theorem {a b : R} {P : R[X]} (hab : a < b) :
    ∃ c ∈ Ioo a b , P.eval b - P.eval a = ((derivative P).eval c) * (b - a) := by
  let Q : R[X] :=  (C (P.eval b) - C (P.eval a)) * (X - C a) - (C b - C a) * (P - C (P.eval a))
  have Q_deriv : derivative Q = (C (P.eval b) - C (P.eval a)) - (C b - C a) * (derivative P) := by
    simp[Q]
  have hQa : Q.eval a = 0 := by simp[Q]
  have hQb : Q.eval b = 0 := by simp[Q] ; ring
  obtain ⟨c, hcmem, hc⟩ := rolle_theorem hab (Eq.trans hQa hQb.symm)
  use c , hcmem
  rw [Q_deriv] at hc
  simp at hc
  linarith

lemma exists_deriv_eq_slope_poly (a b : R) (hab : a < b) (p : Polynomial R) :
    ∃ c : R, c > a ∧ c < b ∧ eval b p - eval a p = (b - a) * eval c (derivative p) := by
  obtain ⟨c, hc1, hc2⟩ := mean_value_theorem hab
  simp at hc1
  obtain ⟨hc_low, hc_high⟩ := hc1
  use c
  refine ⟨hc_low, hc_high, ?_⟩
  rw [hc2]
  have : (b - a) ≠ 0 := by linarith
  field_simp

lemma eval_mod (p q: Polynomial R) (x: R) (h: eval x q = 0) : eval x (p % q) = eval x p := by
  have : eval x (p % q) = eval x (p / q * q) + eval x (p % q) := by simp; exact Or.inr h
  rw [<- eval_add, EuclideanDomain.div_add_mod'] at this; exact this

lemma eval_non_zero (p: Polynomial R) (x: R) (h: eval x p ≠ 0) : p ≠ 0 := by
  simp_all only [ne_eq]
  apply Aesop.BuiltinRules.not_intro
  intro a
  subst a
  simp_all only [eval_zero, not_true_eq_false]

lemma mul_C_eq_root_multiplicity (p: Polynomial R) (c r: R) (hc: ¬ c = 0):
    (rootMultiplicity r p = rootMultiplicity r (C c * p)) := by
  simp only [<-count_roots]
  rw [roots_C_mul]
  exact hc

theorem div_rem_zero {b c r: Polynomial R} (h_rem: r.degree < b.degree) : (c * b + r)/ b = c := by
  rw [mul_comm]
  have h_b : b ≠ 0 := ne_zero_of_degree_gt h_rem
  if H: r = 0 then
   simp [H, h_b]
  else
    have h_stronger : (b * c + r)/b = c ∧ (b * c + r) % b = r := by
      by_contra!
      have h_div_mod: ((b * c + r)/b - c) * b = r - ((b * c + r)% b) := by
       ring_nf
       rw [eq_sub_iff_add_eq, add_rotate, ← eq_sub_iff_add_eq, sub_neg_eq_add]
       simp [EuclideanDomain.div_add_mod]; ring
      have : (b * c + r) / b ≠ c ∧ (b * c + r) % b ≠ r := by
        rw [<- if_false_left]
        split_ifs with H'
        · simp [H', eq_sub_iff_add_eq'] at h_div_mod
          exact this H' h_div_mod
        · intro h_contra
          simp [h_contra, h_b, sub_eq_iff_eq_add] at h_div_mod
          exact H' h_div_mod
      have h_mod_deg : degree ((b * c  + r) % b) < degree b := by
        refine degree_lt_degree ?_
        refine natDegree_mod_lt (b * c + r) ?_
        exact Nat.ne_zero_of_lt ((natDegree_lt_natDegree_iff H).mpr h_rem)
      have h_r : degree (r - (b * c + r)% b) < degree b := by
        have h_max := degree_sub_le r ((b * c + r) % b)
        exact lt_of_le_of_lt h_max (max_lt h_rem h_mod_deg)
      have h_lt_deg : degree b ≤ degree ((b * c + r) / b - c) + degree b := by
        refine le_add_of_nonneg_of_le ?_ ?_
        · exact zero_le_degree_iff.mpr (sub_ne_zero_of_ne this.1)
        · rfl
      have h_div_deg : degree ((b * c + r)/b - c) + degree b = degree (((b * c + r) / b - c) * b) := by
        exact Eq.symm degree_mul
      have h_deg_plus: degree ((b * c + r)/b - c) + degree b = degree (r - (b * c + r)%b) := by
        simp_all
      have h_final : b.degree ≤ degree (r - (b * c + r) % b) := by
        exact le_of_le_of_eq h_lt_deg h_deg_plus
      have h_contra: degree (r - (b * c + r) % b) < degree (r - (b * c + r) % b) := by
        exact Std.lt_of_lt_of_le h_r h_final
      exact (lt_self_iff_false (r - (b * c + r) % b).degree).mp h_contra
    exact h_stronger.1

theorem mul_cancel' {p q r: Polynomial R} (hr: r ≠ 0) : (r * p) / (r * q) = p / q := by
  simp [mul_comm]
  if H: q.natDegree = 0 then
    have ⟨x, h_x⟩ := natDegree_eq_zero.mp H
    rw [<-h_x]
    rw [div_C_mul, mul_div_cancel_right₀ (hb := hr)]
    have : p/ C x = p / (C x * 1) := by rw [mul_one]
    rw [this, div_C_mul]; norm_num
  else
    have hq : q ≠ 0 := Ne.symm (ne_of_apply_ne natDegree fun a => H (id (Eq.symm a)))
    have : p = (p/q) * q + p % q := Eq.symm (EuclideanDomain.div_add_mod' p q)
    rw[this]; ring_nf
    if H': p % q = 0 then
      have h_ne_z : q * r ≠ 0 := (mul_ne_zero_iff_right hr).mpr hq
      simp [H']
      rw [mul_assoc, mul_div_cancel_right₀ (hb := h_ne_z), mul_div_cancel_right₀ (hb := hq)]
    else
      have h_mod_deg : natDegree (p % q) < natDegree q := by
        exact natDegree_mod_lt p H
      have h_mod_r_deg : natDegree ((p % q) * r) < natDegree (q * r) := by
        simp [natDegree_mul, H', hr, hq]
        exact h_mod_deg
      rw [div_rem_zero (degree_lt_degree h_mod_deg), mul_assoc, div_rem_zero (degree_lt_degree h_mod_r_deg)]

lemma mod_eq_sub_div {a b: Polynomial R} : a % b = a - (a/b) * b := by
  have := EuclideanDomain.div_add_mod' a b
  exact eq_sub_of_add_eq' this

theorem mod_mul (p q r: Polynomial R) (hr: r ≠ 0) : (r * p) % (r * q) = r * (p % q) := by
  have : (r * p) % (r * q) = r * p - ((r * p)/(r * q)) * (r * q) := by
    exact mod_eq_sub_div
  ring_nf at this
  rw [mul_cancel' hr, mul_assoc, <-mul_sub, mul_comm q (p/q), <- mod_eq_sub_div (a := p) (b := q)] at this
  exact this

lemma X_sub_C_ne_one (r : R) : X - C r ≠ 1 := by
  rw [sub_eq_neg_add, add_comm, <-C_neg]
  exact X_add_C_ne_one (-r)

lemma rootsInInterval_mul {p q: Polynomial R} (a b: R) (hpq: p * q ≠ 0): rootsInInterval (p * q) a b = rootsInInterval p a b ∪ rootsInInterval q a b := by
  unfold rootsInInterval
  rw [roots_mul hpq, Multiset.toFinset_add]
  exact Finset.filter_union (fun x => x ∈ Ioo a b) p.roots.toFinset q.roots.toFinset

lemma neg_neg_div (p q: Polynomial R) : - (-p/q) = p/q := by
  have: -1 = (-1:R)⁻¹ := Eq.symm inv_neg_one
  calc
    -(-p/q) = -(-1 * p / q) := by simp
    _ = -1 * (-1 * p / q)  := by simp
    _ = -1 * (C (-1) * p / q) := by simp
    _ = (C (-1:R)) * (C (-1) * p / q) := by simp
    _ = (C (-1:R)⁻¹) * (C (-1) * p / q) := by rw [<-this]
    _ = p/q := by
      have hCz : C (-1:R) ≠ 0 := by simp
      rw [<- div_C_mul, mul_cancel' hCz]

lemma mod_minus (p q: Polynomial R) : -p%q = -(p%q) := by
  rw [mod_eq_sub_div, mod_eq_sub_div]
  ring_nf
  calc
    -p - -p / q * q = -p + (- (-p/q * q)) := by ring
    _ = -p + q * (-(-p/q)) := by ring
    _ = -p + q * (p/q) := by rw[neg_neg_div p q]

lemma factorize (a x : R) (ha : a ≠ 0) : x = a * (x / a) := by field_simp

lemma distrib_div (a b d : R) (hd : d ≠ 0) : (a + b) / d = a / d + b / d := by field_simp

lemma sgn_mul_pos (a b : R) (ha : 0 < a) : sgn (a * b) = sgn b := by
  unfold sgn
  split_ifs
  · rfl
  · simp_all only [mul_zero, gt_iff_lt, lt_self_iff_false]
  · simp_all only [gt_iff_lt, mul_pos_iff_of_pos_left]
  · rename_i h h_1 h_2
    simp_all only [gt_iff_lt, lt_self_iff_false, not_false_eq_true, mul_eq_zero, zero_ne_one]
    cases h_1 with
    | inl h =>
      subst h
      simp_all only [lt_self_iff_false]
    | inr h_3 =>
      subst h_3
      simp_all only [lt_self_iff_false]
  · rfl
  · simp_all only [gt_iff_lt, lt_self_iff_false, not_false_eq_true, mul_eq_zero, or_false, not_lt]
  · simp_all only [gt_iff_lt, mul_pos_iff_of_pos_left, not_true_eq_false]
  · simp_all only [mul_zero, gt_iff_lt, lt_self_iff_false, not_false_eq_true, not_true_eq_false]
  · gcongr

lemma sgn_dont_change (a b : R) (hab : abs b < abs a / 2) : sgn (a + b) = sgn a := by
  unfold sgn
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · rfl
  · rw [h3] at hab
    simp at hab
    grind
  · grind
  · have :-a = b := by linarith
    rw [<- this] at hab
    simp at hab
    grind
  · rfl
  · grind
  · grind
  · rw [h8] at hab
    simp at hab
    grind
  · rfl

-- We could have a simpler proof if we had NormedField for RCF
lemma bound_sgn_pos_inf (p : Polynomial R) (hp : p ≠ 0) : ∃ ub : R, ∀ x, x ≥ ub → sgn (eval x p) = sgn_pos_inf p := by
  have r := sum_C_mul_X_pow_eq p
  let n := p.natDegree
  let M := ∑ i ∈ Finset.range n, abs (p.coeff i)
  let ub := (2 * M) / abs (p.leadingCoeff) + 1
  use ub
  intros x hx
  have : 0 ≤ M := by positivity
  have : 0 ≤ (2 * M) / abs p.leadingCoeff := by positivity
  have : 1 ≤ (2 * M) / abs p.leadingCoeff + 1 := by linarith
  have hx2 : 1 ≤ x := Std.IsPreorder.le_trans 1 (2 * M / |p.leadingCoeff| + 1) x this hx
  have h1 : 0 < (2 * M) / abs p.leadingCoeff + 1 := by positivity
  have h2 : 0 < x := by linarith
  have h3 : 0 < x ^ p.natDegree := by positivity
  have h4 : x ^ p.natDegree ≠ 0 := Ne.symm (ne_of_lt h3)
  have hx : x ≠ 0 := by positivity
  have hub1 : 0 < ub := by positivity
  rw [eval_eq_sum_range, sum_range_succ_comm, coeff_natDegree]
  have : p.leadingCoeff * x ^ p.natDegree + ∑ i ∈ Finset.range p.natDegree, p.coeff i * x ^ i =
         x ^ p.natDegree * (p.leadingCoeff + ∑ i ∈ Finset.range p.natDegree, p.coeff i * x ^ ((i : Int) - n)) := by
    rw [factorize _ (p.leadingCoeff * x ^ p.natDegree + ∑ i ∈ Finset.range p.natDegree, p.coeff i * x ^ i) h4]
    simp only [mul_eq_mul_left_iff, pow_eq_zero_iff', ne_eq]
    left
    rw [distrib_div]
    have : p.leadingCoeff * x ^ p.natDegree / x ^ p.natDegree = p.leadingCoeff := by field_simp
    rw [this]
    · simp only [add_right_inj]
      rw [sum_div]
      congr
      ext i
      field_simp
      unfold n
      rw [mul_assoc]
      have : x ^ p.natDegree = x ^ (p.natDegree : Int) := by
        simp
      have : x ^ p.natDegree * x ^ ((i : Int) - p.natDegree) = x ^ i := by
        rw [this]
        rw [<- zpow_add₀ hx _ _]
        norm_num
      rw [this]
    · exact h4
  rw [this, sgn_mul_pos _ _ h3]
  have ineq : abs (∑ i ∈ Finset.range p.natDegree, p.coeff i * x ^ ((i : Int) - n)) ≤ M / x := by
    unfold M
    refine le_trans (abs_sum_le_sum_abs _ _) ?_
    rw [sum_div]
    gcongr
    next j hj =>
      norm_num
      have : abs x = x := abs_of_pos h2
      rw [this]
      field_simp
      rw [mul_assoc]
      have : x ^ ((j : Int) - n) * x = x ^ ((j : Int) - n + 1) := Eq.symm (zpow_add_one₀ hx (↑j - ↑n))
      rw [this]
      have : (j : Int) - n + 1 ≤ 0 := by
        simp at hj
        linarith
      have : x ^ ((j : Int) - n + 1) ≤ 1 := zpow_le_one_of_nonpos₀ hx2 this
      have pos : 0 ≤ abs (p.coeff j) := abs_nonneg (p.coeff j)
      exact mul_le_of_le_one_right pos this
  have H1 : M / ub < abs p.leadingCoeff / 2 := by
    unfold ub
    have : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
    field_simp
    simp_all only [ne_eq, ge_iff_le, le_add_iff_nonneg_left, pow_pos, pow_eq_zero_iff', false_and,
      not_false_eq_true, leadingCoeff_eq_zero, lt_add_iff_pos_right, abs_pos]
  have : M / x ≤ M / ub := by gcongr
  have : M / x < abs p.leadingCoeff / 2 := Std.lt_of_le_of_lt this H1
  have key : abs (∑ i ∈ Finset.range p.natDegree, p.coeff i * x ^ ((i : Int) - n)) < abs p.leadingCoeff / 2 := Std.lt_of_le_of_lt ineq this
  rw [sgn_dont_change _ _ key, sgn_pos_inf]

lemma bound_sgn_neg_inf (p : Polynomial R) (hp : p ≠ 0) : ∃ lb : R, ∀ x, x ≤ lb → sgn (eval x p) = sgn_neg_inf p := by
  obtain ⟨s, hs⟩ : ∃ s, p.eval s ≠ 0 := by
    contrapose! hp
    exact zero_of_eval_zero p hp
  let p' := Polynomial.comp p (-Polynomial.X)
  obtain ⟨s, hs⟩ : ∃ s, p'.eval s ≠ 0 := by
    use -s
    unfold p'
    simp
    assumption
  have : p' ≠ 0 := by
    intro abs
    have ev_0 : eval s p' = 0 := by
      rw [abs]
      simp
    exact hs ev_0
  obtain ⟨ub, hub⟩  := bound_sgn_pos_inf (Polynomial.comp p (-Polynomial.X)) this
  rw [sgn_inf_comp]
  use -ub
  intros x hx
  have := hub (-x) (by linarith)
  simp at this
  exact this

lemma root_ub (p : Polynomial R) (hp : p ≠ 0) :
    ∃ ub, (∀ x, eval x p = 0 → x < ub) ∧ (∀ x, x ≥ ub → sgn (eval x p) = sgn_pos_inf p) := by
  obtain ⟨ub1, hub1⟩ : ∃ ub1, ∀ x, eval x p = 0 → x < ub1 := by
    by_cases ∃ r, eval r p = 0
    next H =>
      let roots := p.roots.toFinset
      obtain ⟨r, hr⟩ := H
      have : r ∈ p.roots.toFinset := Multiset.mem_toFinset.mpr ((mem_roots_iff_aeval_eq_zero hp).mpr hr)
      have : roots.Nonempty := by tauto
      obtain ⟨max_r, hm⟩ := Finset.max_of_nonempty this
      have : ∀ x, eval x p = 0 → x ≤ max_r := by
        intros x hx
        have := Multiset.mem_toFinset.mpr ((mem_roots_iff_aeval_eq_zero hp).mpr hx)
        exact Finset.le_max_of_eq this hm
      use max_r + 1
      intros x hx
      have := this x hx
      linarith
    next H =>
      use 0
      intros x hx
      aesop
  obtain ⟨ub2, hub2⟩ : ∃ ub2, ∀ x, x ≥ ub2 → sgn (eval x p) = sgn_pos_inf p := bound_sgn_pos_inf p hp
  let ub := Max.max ub1 ub2
  have : ub1 ≤ ub := le_max_left ub1 ub2
  have : ub2 ≤ ub := le_max_right ub1 ub2
  use ub
  constructor
  · intros x hx
    have := hub1 x hx
    linarith
  · intros x hx
    exact hub2 x (by linarith)

lemma root_lb (p : Polynomial R) (hp : p ≠ 0) :
    ∃ lb, (∀ x, eval x p = 0 → x > lb) ∧ (∀ x, x ≤ lb → sgn (eval x p) = sgn_neg_inf p) := by
  obtain ⟨lb1, hlb1⟩ : ∃ lb1, ∀ x, eval x p = 0 → x > lb1 := by
    by_cases ∃ r, eval r p = 0
    next H =>
      let roots := p.roots.toFinset
      obtain ⟨r, hr⟩ := H
      have : r ∈ p.roots.toFinset := Multiset.mem_toFinset.mpr ((mem_roots_iff_aeval_eq_zero hp).mpr hr)
      have : roots.Nonempty := by tauto
      obtain ⟨min_r, hm⟩ := Finset.min_of_nonempty this
      have : ∀ x, eval x p = 0 → x ≥ min_r := by
        intros x hx
        have := Multiset.mem_toFinset.mpr ((mem_roots_iff_aeval_eq_zero hp).mpr hx)
        exact Finset.min_le_of_eq this hm
      use min_r - 1
      intros x hx
      have := this x hx
      linarith
    next H =>
      use 0
      intros x hx
      aesop
  obtain ⟨lb2, hlb2⟩ : ∃ lb2, ∀ x, x ≤ lb2 → sgn (eval x p) = sgn_neg_inf p := bound_sgn_neg_inf p hp
  let lb := Min.min lb1 lb2
  have : lb ≤ lb1 := min_le_left lb1 lb2
  have : lb ≤ lb2 := min_le_right lb1 lb2
  use lb
  constructor
  · intros x hx
    have := hlb1 x hx
    linarith
  · intros x hx
    exact hlb2 x (by linarith)

lemma root_list_ub (ps : List (Polynomial R)) (a : R) (h0 : 0 ∉ ps) :
    ∃ ub : R,
      ((∀ p ∈ ps, ∀ x : R, eval x p = 0 → x < ub) ∧
       (a < ub) ∧
       (∀ x : R, x ≥ ub → ∀ p ∈ ps, sgn (eval x p) = sgn_pos_inf p)) := by
  cases ps
  next => simp; exact exists_gt a
  next p ps =>
    have p_not_zero : p ≠ 0 := Ne.symm (List.ne_of_not_mem_cons h0)
    have not_zero : 0 ∉ ps := List.not_mem_of_not_mem_cons h0
    obtain ⟨ub1, hub1, hub2, hub3⟩ := root_list_ub ps a not_zero
    obtain ⟨ub2, hub21, hub22⟩ := root_ub p p_not_zero
    let ub := Max.max ub1 ub2
    have : ub1 ≤ ub := le_max_left ub1 ub2
    have : ub2 ≤ ub := le_max_right ub1 ub2
    use ub
    constructor
    · intros pp hpp x hx
      have : pp = p ∨ pp ∈ ps := List.mem_cons.mp hpp
      cases this
      next hmem =>
        rw [hmem] at hx
        exact lt_sup_of_lt_right (hub21 x hx)
      next hmem => exact lt_sup_of_lt_left (hub1 pp hmem x hx)
    · constructor
      · linarith
      · intros x hx pp hpp
        have : pp = p ∨ pp ∈ ps := List.mem_cons.mp hpp
        cases this
        next hmem =>
          rw [hmem]
          exact hub22 x (by linarith)
        next hmem =>
          exact hub3 x (by linarith) pp hmem

lemma root_list_lb (ps : List (Polynomial R)) (b : R) (h0 : 0 ∉ ps) :
    ∃ lb : R,
      ((∀ p ∈ ps, ∀ x : R, eval x p = 0 → lb < x) ∧
       (lb < b) ∧
       (∀ x : R, x ≤ lb → ∀ p ∈ ps, sgn (eval x p) = sgn_neg_inf p)) := by
  cases ps
  next => simp; exact exists_lt b
  next p ps =>
    have p_not_zero : p ≠ 0 := Ne.symm (List.ne_of_not_mem_cons h0)
    have not_zero : 0 ∉ ps := List.not_mem_of_not_mem_cons h0
    obtain ⟨lb1, hlb1, hlb2, hlb3⟩ := root_list_lb ps b not_zero
    obtain ⟨lb2, hlb21, hlb22⟩ := root_lb p p_not_zero
    let lb := Min.min lb1 lb2
    have : lb ≤ lb1 := min_le_left lb1 lb2
    have : lb ≤ lb2 := min_le_right lb1 lb2
    use lb
    constructor
    · intros pp hpp x hx
      have : pp = p ∨ pp ∈ ps := List.mem_cons.mp hpp
      cases this
      next hmem =>
        rw [hmem] at hx
        exact inf_lt_of_right_lt (hlb21 x hx)
      next hmem => exact inf_lt_of_left_lt (hlb1 pp hmem x hx)
    · constructor
      · exact inf_lt_of_left_lt hlb2
      · intros x hx pp hpp
        have : pp = p ∨ pp ∈ ps := List.mem_cons.mp hpp
        cases this
        next hmem =>
          rw [hmem]
          apply hlb22
          linarith
        next hmem =>
          apply hlb3
          · linarith
          · exact hmem

