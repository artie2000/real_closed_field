/-
Copyright (c) 2026 Pedro Saccomani, Sarah Pereira and Tomaz Mascarenhas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pedro Saccomani, Sarah Pereira, Tomaz Mascarenhas
-/
import RealClosedField.SturmTarski.SturmSeq

noncomputable section

open Polynomial

variable {R : Type*}
variable [Field R] [IsRealClosed R]

theorem sturm_tarski_interval (a b : R) (p q : Polynomial R) (hab : a < b) (hpa : eval a p ≠ 0) (hpb : eval b p ≠ 0) :
    tarskiQuery p q a b = seqVarSturm_ab p (derivative p * q) a b := by
  rw [cauchyIndex_sturmSeq p (derivative p * q) a b hpa hpb hab]
  rw [cauchyIndex_poly_taq p q a b]

def rootsAbove (f : Polynomial R) (a : R) : Finset R :=
  f.roots.toFinset.filter (fun x => x > a)

def tarskiQuery_above (p q : Polynomial R) (a : R) : ℤ :=
  ∑ x ∈ rootsAbove p a, sgn (q.eval x)

def rootsBelow (f : Polynomial R) (b : R) : Finset R :=
  f.roots.toFinset.filter (fun x => x < b)

def tarskiQuery_below (p q : Polynomial R) (b : R) : ℤ :=
  ∑ x ∈ rootsBelow p b, sgn (q.eval x)

def tarskiQuery_R (p q : Polynomial R) : ℤ :=
  ∑ x ∈ p.roots.toFinset, sgn (q.eval x)

lemma seq_sgn_pos_inf_seqEvalSgn (ub : R) (ps : List (Polynomial R)) (key : ∀ x ≥ ub, ∀ pp ∈ ps, sgn (eval x pp) = sgn_pos_inf pp) :
    seq_sgn_pos_inf ps = seqEvalSgn ub ps := by
  cases ps
  next => simp only [seq_sgn_pos_inf, seqEvalSgn]
  next hd tl =>
    simp only [seq_sgn_pos_inf, seqEvalSgn, List.cons.injEq, Int.cast_inj]
    constructor
    · apply Eq.symm
      apply key
      · exact Preorder.le_refl ub
      · exact List.mem_cons_self
    · apply seq_sgn_pos_inf_seqEvalSgn ub tl
      intros x hx pp hpp
      apply key
      · exact hx
      · exact List.mem_cons_of_mem hd hpp

theorem sturm_tarski_above (a : R) (p q : Polynomial R) (hpa : eval a p ≠ 0) :
    tarskiQuery_above p q a = seqVarAboveSturm p (derivative p * q) a := by
  let ps := sturmSeq p (derivative p * q)
  have ps_def : ps = sturmSeq p (derivative p * q) := rfl
  have : p ≠ 0 := eval_non_zero p a hpa
  have : p ∈ ps := by
    unfold ps sturmSeq
    simp [this]
  obtain ⟨ub, hub1, hub2, hub3⟩ : ∃ ub,
      (∀ pp ∈ ps, (∀ x, eval x pp = 0 → x < ub)) ∧
      a < ub ∧
      (∀ x, x ≥ ub → (∀ pp ∈ ps, sgn (eval x pp) = sgn_pos_inf pp)) := by
    apply root_list_ub
    exact no_zero_in_sturmSeq p (derivative p * q)
  have taq_taq : tarskiQuery_above p q a = tarskiQuery p q a ub := by
    simp only [tarskiQuery_above, tarskiQuery]
    congr
    simp only [rootsAbove, rootsInInterval]
    ext z
    simp only [gt_iff_lt, Finset.mem_filter, Multiset.mem_toFinset, mem_roots', ne_eq, IsRoot.def,
      Set.mem_Ioo, and_congr_right_iff, iff_self_and, and_imp]
    intro a_1 a_2 a_3
    simp_all only [ne_eq, not_false_eq_true, ge_iff_le, ps]
    apply hub1
    on_goal 2 => { exact a_2 }
    · simp_all only
  have changes_changes : seqVarAboveSturm p (derivative p * q) a = seqVarSturm_ab p (derivative p * q) a ub := by
    simp [seqVarSturm_ab, seqVarAboveSturm, seqVarAbove_a, seqVar_ab]
    rw [seqVarSgn, <- ps_def, seq_sgn_pos_inf_seqEvalSgn ub ps hub3]
  rw [taq_taq, changes_changes]
  apply sturm_tarski_interval _ _ _ _ hub2 hpa
  intro abs
  have := hub1 p this ub abs
  simp at this

lemma seq_sgn_neg_inf_seqEvalSgn (lb : R) (ps : List (Polynomial R)) (key : ∀ x ≤ lb, ∀ pp ∈ ps, sgn (eval x pp) = sgn_neg_inf pp) :
    seq_sgn_neg_inf ps = seqEvalSgn lb ps := by
  cases ps
  next => simp only [seq_sgn_neg_inf, seqEvalSgn]
  next hd tl =>
    simp only [seq_sgn_neg_inf, seqEvalSgn, List.cons.injEq, Int.cast_inj]
    constructor
    · apply Eq.symm
      exact key _ (Preorder.le_refl lb) _ List.mem_cons_self
    · apply seq_sgn_neg_inf_seqEvalSgn lb tl
      intros x hx pp hpp
      exact key _ hx _ (List.mem_cons_of_mem hd hpp)

theorem sturm_tarski_below (b : R) (p q : Polynomial R) (hpa : eval b p ≠ 0) :
    tarskiQuery_below p q b = seqVarBelowSturm p (derivative p * q) b := by
  let ps := sturmSeq p (derivative p * q)
  have ps_def : ps = sturmSeq p (derivative p * q) := rfl
  have : p ≠ 0 := eval_non_zero p b hpa
  have : p ∈ ps := by
    unfold ps sturmSeq
    simp [this]
  obtain ⟨lb, hlb1, hlb2, hlb3⟩ : ∃ lb,
      (∀ pp ∈ ps, (∀ x, eval x pp = 0 → x > lb)) ∧
      b > lb ∧
      (∀ x, x ≤ lb → (∀ pp ∈ ps, sgn (eval x pp) = sgn_neg_inf pp)) := by
    apply root_list_lb
    exact no_zero_in_sturmSeq p (derivative p * q)
  have taq_taq : tarskiQuery_below p q b = tarskiQuery p q lb b := by
    simp [tarskiQuery_below, tarskiQuery]
    congr
    simp [rootsBelow, rootsInInterval]
    ext z
    simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots', ne_eq, IsRoot.def,
      and_congr_right_iff, iff_and_self, and_imp]
    intro a a_1 a_2
    simp_all only [ne_eq, not_false_eq_true, gt_iff_lt, ps]
    apply hlb1
    on_goal 2 => { exact a_1 }
    simp_all only
  have changes_changes : seqVarBelowSturm p (derivative p * q) b = seqVarSturm_ab p (derivative p * q) lb b := by
    simp [seqVarSturm_ab, seqVarBelowSturm, seqVarBelow_b, seqVar_ab]
    rw [seqVarSgn, <- ps_def, seq_sgn_neg_inf_seqEvalSgn lb ps hlb3]
  rw [taq_taq, changes_changes]
  apply sturm_tarski_interval _ _ _ _ hlb2 _ hpa
  intro abs
  have := hlb1 p this lb abs
  simp at this

theorem sturm_tarski_R (p q : Polynomial R) :
    tarskiQuery_R p q = seqVarRSturm p (derivative p * q) := by
  if hp: p = 0 then
    rw [hp]
    simp [tarskiQuery_R, seqVarRSturm, seqVarR, seq_sgn_neg_inf, seq_sgn_pos_inf]
  else
    let ps := sturmSeq p (derivative p * q)
    have ps_def : ps = sturmSeq p (derivative p * q) := rfl
    have : p ∈ ps := by
      unfold ps sturmSeq
      simp [hp]
    obtain ⟨lb, hlb1, hlb2, hlb3⟩ : ∃ lb,
        (∀ pp ∈ ps, (∀ x, eval x pp = 0 → x > lb)) ∧
        0 > lb ∧
        (∀ x, x ≤ lb → (∀ pp ∈ ps, sgn (eval x pp) = sgn_neg_inf pp)) := by
      apply root_list_lb
      exact no_zero_in_sturmSeq p (derivative p * q)
    obtain ⟨ub, hub1, hub2, hub3⟩ : ∃ ub,
        (∀ pp ∈ ps, (∀ x, eval x pp = 0 → x < ub)) ∧
        0 < ub ∧
        (∀ x, x ≥ ub → (∀ pp ∈ ps, sgn (eval x pp) = sgn_pos_inf pp)) := by
      apply root_list_ub
      exact no_zero_in_sturmSeq p (derivative p * q)
    have taq_taq : tarskiQuery_R p q = tarskiQuery p q lb ub := by
      simp [tarskiQuery_R, tarskiQuery]
      congr
      unfold rootsInInterval
      ext z
      simp only [Multiset.mem_toFinset, mem_roots', ne_eq, IsRoot.def, Set.mem_Ioo,
        Finset.mem_filter, iff_self_and, and_imp]
      intro a a_1
      simp_all only [not_false_eq_true, gt_iff_lt, ge_iff_le, ps]
      apply And.intro
      · apply hlb1
        on_goal 2 => { exact a_1 }
        · simp_all only
      · apply hub1
        · exact this
        · simp_all only
    have changes_changes : seqVarRSturm p (derivative p * q) = seqVarSturm_ab p (derivative p * q) lb ub := by
      simp [seqVarRSturm, seqVarR, seqVarSturm_ab, seqVar_ab]
      rw [ seqVarSgn
         , seqVarSgn
         , <- ps_def
         , seq_sgn_neg_inf_seqEvalSgn lb ps hlb3
         , seq_sgn_pos_inf_seqEvalSgn ub ps hub3
         ]
    have lb_neq_0 : eval lb p ≠ 0 := by
      intro abs
      have := hlb1 p this lb abs
      simp at this
    have ub_neq_0 : eval ub p ≠ 0 := by
      intro abs
      have := hub1 p this ub abs
      simp at this
    have lb_ub : lb < ub := by linarith
    rw [taq_taq, changes_changes]
    exact sturm_tarski_interval lb ub p q lb_ub lb_neq_0 ub_neq_0

