import RealClosedField.SturmTarski.SturmSeq

open Polynomial Set Filter Classical

noncomputable section

variable {R : Type*}
variable [Field R] [IsRealClosed R]

lemma changes_smods_congr (p q : Polynomial R) (a a' : R) (haa' : a ≠ a') (hpa : eval a p ≠ 0)
    (no_root : ∀ p' ∈ sturmSeq p q, ∀ x : R, ((a < x ∧ x ≤ a') ∨ (a' ≤ x ∧ x < a)) → eval x p' ≠ 0) :
    seqVar (seqEval a (sturmSeq p q)) = seqVar (seqEval a' (sturmSeq p q)) := by
  have p_neq_0 : p ≠ 0 := eval_non_zero p a hpa
  let r1 := -p%q
  have r1_def : r1 = -p%q := rfl
  have a_a'_rel: ∀ pp ∈ sturmSeq p q, eval a pp * eval a' pp ≥ 0 := by
    by_contra!
    obtain ⟨pp, hpp1, hpp2⟩ := this
    if haa': a < a' then
      obtain ⟨x, hx1, hx2, hx3⟩ : ∃ x : R, a < x ∧ x < a' ∧ eval x pp = 0 := exists_root_ioo_mul (le_of_lt haa') hpp2
      have := no_root pp hpp1 x (Or.inl (And.intro hx1 (le_of_lt hx2)))
      exact this hx3
    else
      simp at haa'
      rw [mul_comm] at hpp2
      obtain ⟨x, hx1, hx2, hx3⟩ : ∃ x : R, a' < x ∧ x < a ∧ eval x pp = 0 := exists_root_ioo_mul haa' hpp2
      have := no_root pp hpp1 x (Or.inr (And.intro (le_of_lt hx1) hx2))
      exact this hx3

  if hq: q = 0 then
    unfold sturmSeq
    simp [hq, seqEval, seqVar, p_neq_0]
  else if hq2: eval a q = 0 then
    let r2 := -(q%r1)
    have : eval a p = - (eval a r1) := by
      have h1 := EuclideanDomain.quotient_mul_add_remainder_eq p q
      have h2 : r1 = EuclideanDomain.remainder (-p) q := by rfl
      have : eval a p = eval a (q * EuclideanDomain.quotient p q + EuclideanDomain.remainder p q) := by
        congr
        exact (Eq.symm h1)
      rw [this]
      simp [hq2]
      rw [h2]
      have : ∀ p q : Polynomial R, EuclideanDomain.remainder p q = p % q := by intros p q; rfl
      rw [this, this (-p) q, mod_minus]
      simp
    have : eval a r1 = -eval a p := by linarith
    have h_eval_r : eval a r1 ≠ 0 := by rw [this]; exact neg_ne_zero.mpr hpa
    have r_neq_0 : r1 ≠ 0 := eval_non_zero r1 a h_eval_r
    have eval_a_eval_r : eval a p * eval a r1 < 0 := by rw [this]; simp; exact hpa
    obtain ⟨ps, hps1, hps2⟩ : ∃ ps, sturmSeq p q = p :: q :: r1 :: ps ∧ sturmSeq r1 r2 = r1 :: ps := by
      unfold sturmSeq
      simp [p_neq_0, r_neq_0]
      rw [<- r1_def]
      nth_rw 1 [sturmSeq]
      simp [hq]
      nth_rw 1 [sturmSeq]
      split_ifs
      next h => exact r_neq_0 h
      next h =>
        congr <;> exact mod_minus q r1
    have : List.length (sturmSeq r1 r2) < List.length (sturmSeq p q) := by simp [hps1, hps2]
    have no_root_2_aux := no_root
    rw [hps1] at no_root_2_aux
    have no_root_2 : ∀ p' ∈ sturmSeq r1 r2, ∀ (x : R), a < x ∧ x ≤ a' ∨ a' ≤ x ∧ x < a → eval x p' ≠ 0 := by
      rw [hps2]
      clear * - no_root_2_aux
      intros p' hp'
      have : p' ∈ p :: q :: r1 :: ps := by
        simp
        right
        right
        simp at hp'
        exact hp'
      exact no_root_2_aux p' this
    have IH := changes_smods_congr r1 r2 a a' haa' h_eval_r no_root_2
    have rec_a : seqVar (seqEval a (sturmSeq p q)) = 1 + seqVar (seqEval a (sturmSeq r1 r2)) := by
      rw [hps1, hps2, seqEval, seqEval]
      simp [seqVar, hq2]
      rw [seqEval, seqVar]
      simp [h_eval_r]
      exact eval_a_eval_r
    have rec_a' : seqVar (seqEval a' (sturmSeq p q)) = 1 + seqVar (seqEval a' (sturmSeq r1 r2)) := by
      have hp1 : eval a p * eval a' p ≥ 0 := by
        rw [hps1] at a_a'_rel
        apply a_a'_rel
        exact List.mem_cons_self
      have hr1 : eval a r1 * eval a' r1 ≥ 0 := by
        rw [hps1] at a_a'_rel
        apply a_a'_rel
        simp only [List.mem_cons, true_or, or_true]
      have ev_neq_0_p : eval a' p ≠ 0 := by
        rw [hps1] at no_root
        apply no_root p List.mem_cons_self
        aesop
      have ev_neq_0_r1 : eval a' r1 ≠ 0 := by
        rw [hps1] at no_root
        apply no_root r1
        · simp only [List.mem_cons, true_or, or_true]
        · aesop
      have ev_neq_0_q : eval a' q ≠ 0 := by
        rw [hps1] at no_root
        apply no_root q
        · simp only [List.mem_cons, true_or, or_true]
        · aesop
      rw [hps1, hps2]
      rw [seqEval, seqEval, seqEval]
      rw [seqVar]
      simp [ev_neq_0_q]
      split_ifs
      next H =>
        simp [seqVar, ev_neq_0_r1]
        by_contra!
        have : (eval a' p * eval a' q) * (eval a' q * eval a' r1) > 0 := mul_pos_of_neg_of_neg H this
        have h1 : (eval a' p * eval a' r1) * (eval a' q * eval a' q) > 0 := by admit
        have h2 : eval a' q * eval a' q > 0 := mul_self_pos.mpr ev_neq_0_q
        have h_pos : eval a' p * eval a' r1 > 0 := (pos_iff_pos_of_mul_pos h1).mpr h2
        have : (eval a p * eval a' p) * (eval a r1 * eval a' r1) ≥ 0 := Left.mul_nonneg hp1 hr1
        have : (eval a p * eval a r1) * (eval a' p * eval a' r1) ≥ 0 := by linarith
        have : eval a p * eval a r1 ≥ 0 := (mul_nonneg_iff_of_pos_right h_pos).mp this
        linarith
        admit
      next H =>
        simp [seqVar, ev_neq_0_r1]
        admit
        /- simp at H -/
        /- by_contra! -/
        /- have : 0 ≤ (eval a' p * eval a' q) * (eval a' q * eval a' r1) := Left.mul_nonneg H this -/
        /- have h1 : 0 ≤ (eval a' p * eval a' r1) * (eval a' q * eval a' q) := by linarith -/
        /- have h2 : 0 < eval a' q * eval a' q := mul_self_pos.mpr ev_neq_0_q -/
        /- have h_pos : 0 ≤ eval a' p * eval a' r1 := (mul_nonneg_iff_of_pos_right h2).mp h1 -/
        /- have ev_pos : 0 < eval a' p * eval a' r1 := by -/
        /-   by_contra! -/
        /-   have : 0 = eval a' p * eval a' r1 := by linarith -/
        /-   have : eval a' p = 0 ∨ eval a' r1 = 0 := mul_eq_zero.mp (id (Eq.symm this)) -/
        /-   cases this -/
        /-   next inl => exact ev_neq_0_p inl -/
        /-   next inr => exact ev_neq_0_r1 inr -/
        /- have : (eval a p * eval a' p) * (eval a r1 * eval a' r1) ≥ 0 := Left.mul_nonneg hp1 hr1 -/
        /- have : (eval a p * eval a r1) * (eval a' p * eval a' r1) ≥ 0 := by linarith -/
        /- have : eval a p * eval a r1 ≥ 0 := (mul_nonneg_iff_of_pos_right ev_pos).mp this -/
        /- linarith -/
    rw [rec_a, rec_a', IH]
  else
    obtain ⟨ps, hps1, hps2⟩ : ∃ ps, sturmSeq p q = p :: q :: ps ∧ sturmSeq q r1 = q :: ps := by
      rw [sturmSeq]
      admit
      /- simp [p_neq_0] -/
      /- rw [sturmSeq] -/
      /- simp [hq] -/
    have : List.length (sturmSeq q r1) < List.length (sturmSeq p q) := by
      rw [hps1, hps2]
      admit
      /- simp -/
    have no_root_2_aux := no_root
    rw [hps1] at no_root_2_aux
    have no_root_2 : ∀ p' ∈ sturmSeq q r1, ∀ (x : R), a < x ∧ x ≤ a' ∨ a' ≤ x ∧ x < a → eval x p' ≠ 0 := by
      rw [hps2]
      clear * - no_root_2_aux
      intros p' hp'
      have : p' ∈ p :: q :: ps := List.mem_cons_of_mem p hp'
      exact no_root_2_aux p' this
    have IH := changes_smods_congr q r1 a a' haa' hq2 no_root_2
    have hpa' : eval a' p ≠ 0 := by
      apply no_root p (by rw [hps1]; exact List.mem_cons_self)
      aesop
    have hqa' : eval a' q ≠ 0 := by
      apply no_root q (by rw [hps1]; simp)
      aesop
    have ev_pa' : eval a p * eval a' p ≥ 0 := by
      apply a_a'_rel p (by rw [hps1]; exact List.mem_cons_self)
    have ev_qa' : eval a q * eval a' q ≥ 0 := by
      apply a_a'_rel q (by rw [hps1]; simp)
    rw [hps1]
    simp [seqEval, seqVar, hq2, hqa']
    have eq_a : seqVar (eval a q :: seqEval a ps) = seqVar (seqEval a (q :: ps)) := by simp [seqEval]
    have eq_a' : seqVar (eval a' q :: seqEval a' ps) = seqVar (seqEval a' (q :: ps)) := by simp [seqEval]
    rw [hps2] at IH
    split_ifs
    next h1 h2 => rw [eq_a, eq_a', IH]
    next h1 h2 =>
      push_neg at h2
      clear * - h1 h2 ev_pa' ev_qa' hq2 hpa hpa' hqa'
      by_cases eval a p > 0
      next h_evap =>
        have Ha'p : eval a' p > 0 := by
          by_contra!
          have : eval a' p < 0 := lt_of_le_of_ne this hpa'
          have : eval a p * eval a' p < 0 := mul_neg_of_pos_of_neg h_evap this
          linarith
        have Haq : eval a q < 0 := by
          by_contra!
          have : eval a q > 0 := lt_of_le_of_ne this fun a_1 => hq2 (Eq.symm a_1)
          have : eval a p * eval a q > 0 := Left.mul_pos h_evap this
          linarith
        have Ha'q : eval a' q < 0 := by
          by_contra!
          have : eval a' q > 0 := lt_of_le_of_ne this (Ne.symm hqa')
          have : eval a q * eval a' q < 0 := mul_neg_of_neg_of_pos Haq this
          linarith
        have : eval a' q * eval a' p < 0 := mul_neg_of_neg_of_pos Ha'q Ha'p
        linarith
      next h_evap =>
        push_neg at h_evap
        have h_evap : eval a p < 0 := lt_of_le_of_ne h_evap hpa
        have Ha'p : eval a' p < 0 := by
          by_contra!
          have : eval a' p > 0 := lt_of_le_of_ne this (id (Ne.symm hpa'))
          have : eval a p * eval a' p < 0 := mul_neg_of_neg_of_pos h_evap this
          linarith
        have Haq : eval a q > 0 := by
          by_contra!
          have : eval a q < 0 := lt_of_le_of_ne this hq2
          have : eval a p * eval a q > 0 := mul_pos_of_neg_of_neg h_evap this
          linarith
        have Ha'q : eval a' q > 0 := by
          by_contra!
          have : eval a' q < 0 := lt_of_le_of_ne this hqa'
          have : eval a q * eval a' q < 0 := mul_neg_of_pos_of_neg Haq this
          linarith
        have : eval a' p * eval a' q < 0 := mul_neg_of_neg_of_pos Ha'p Ha'q
        linarith
    next h1 h2 =>
      clear * - h1 h2 ev_pa' ev_qa' hq2 hpa hpa' hqa'
      by_cases eval a p > 0
      next h_evap =>
        have Ha'p : eval a' p > 0 := by
          by_contra!
          have : eval a' p < 0 := lt_of_le_of_ne this hpa'
          have : eval a p * eval a' p < 0 := mul_neg_of_pos_of_neg h_evap this
          linarith
        have Haq : eval a q > 0 := by
          by_contra!
          have : eval a q < 0 := lt_of_le_of_ne this hq2
          have : eval a p * eval a q < 0 := mul_neg_of_pos_of_neg h_evap this
          linarith
        have Ha'q : eval a' q > 0 := by
          by_contra!
          have : eval a' q < 0 := (pos_iff_neg_of_mul_neg h2).mp Ha'p
          have : eval a q * eval a' q < 0 := mul_neg_of_pos_of_neg Haq this
          linarith
        have : eval a' q * eval a' p > 0 := Left.mul_pos Ha'q Ha'p
        linarith
      next h_evap =>
        push_neg at h_evap
        have h_evap : eval a p < 0 := lt_of_le_of_ne h_evap hpa
        have Ha'p : eval a' p < 0 := by
          by_contra!
          have : eval a' p > 0 := lt_of_le_of_ne this (id (Ne.symm hpa'))
          have : eval a p * eval a' p < 0 := mul_neg_of_neg_of_pos h_evap this
          linarith
        have Haq : eval a q < 0 := by
          by_contra!
          have : eval a q > 0 := lt_of_le_of_ne this fun a_1 => hq2 (id (Eq.symm a_1))
          have : eval a p * eval a q < 0 := mul_neg_of_neg_of_pos h_evap this
          linarith
        have Ha'q : eval a' q < 0 := by
          by_contra!
          have : eval a' q > 0 := (neg_iff_pos_of_mul_neg h2).mp Ha'p
          have : eval a q * eval a' q < 0 := mul_neg_of_neg_of_pos Haq this
          linarith
        have : eval a' p * eval a' q > 0 := mul_pos_of_neg_of_neg Ha'p Ha'q
        linarith
    next h1 h2 => rw [eq_a, eq_a', IH]
termination_by List.length (sturmSeq p q)

