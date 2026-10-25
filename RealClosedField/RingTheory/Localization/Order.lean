import RealClosedField.Upstream

/- TODO : ordering on an ID <-> ordering on its fraction field -/
/- TODO : more generally, orderings on a localization at `s` correspond to
          orderings with support disjoint from `s` -/

-- TODO : change upstream
attribute [simp] Localization.liftOn_mk

theorem nontrivial_localization_iff_le_nonZeroDivisors
    {R : Type*} [CommRing R] [IsDomain R] {s : Submonoid R} :
    Nontrivial (Localization s) ↔ s ≤ nonZeroDivisors R := by
  grind [OreLocalization.nontrivial_iff, IsConcreteLE.le_iff, mem_nonZeroDivisors_iff_ne_zero]

theorem le_nonZeroDivisors_of_nontrivial_localization
    {R : Type*} [CommRing R] [IsDomain R]
    (s : Submonoid R) [i : Nontrivial (Localization s)] :
    s ≤ nonZeroDivisors R := nontrivial_localization_iff_le_nonZeroDivisors.mp i

namespace Localization

theorem coe_denom_ne_zero {R : Type*} [CommRing R] {s : Submonoid R} [Nontrivial (Localization s)]
    (a : s) : (a : R) ≠ 0 := by grind [OreLocalization.nontrivial_iff]

theorem r_iff_of_nontrivial {R : Type*} [CommRing R] [IsDomain R] {s : Submonoid R}
    [Nontrivial (Localization s)] (a c : R) (b d : s) : (r s) (a, b) (c, d) ↔ a * d = b * c :=
  r_iff_of_le_nonZeroDivisors (le_nonZeroDivisors_of_nontrivial_localization _) ..

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (s : Submonoid R)
  [Nontrivial (Localization s)]

@[reducible] def nonneg_priv : Subsemiring (Localization s) where
  carrier := .ofPred fun x ↦ liftOn x (fun a₁ a₂ ↦ 0 ≤ a₁ * (a₂ : R))
      fun {a₁ b₁ a₂ b₂} hab ↦ propext <| by
    rw [r_iff_of_nontrivial] at hab
    have hsq_pos (x : s) : 0 < (x : R) * x := by
      grind [mul_self_pos, coe_denom_ne_zero]
    calc
      _ ↔ _ := (mul_nonneg_iff_of_pos_right (hsq_pos b₂)).symm
      _ ↔ _ := by grind
      _ ↔ _ := mul_nonneg_iff_of_pos_right (hsq_pos a₂)
  zero_mem' := by simp [← mk_zero 1]
  one_mem' := by simp [← mk_one]
  add_mem' {x y} := induction_on₂ x y fun x y hx hy ↦ by
    simp_rw [Set.mem_ofPred_eq, add_mk, liftOn_mk, Submonoid.coe_mul] at *
    suffices 0 ≤ x.1 * x.2 * y.2 ^ 2 + y.1 * y.2 * x.2 ^ 2 by grind
    positivity
  mul_mem' {x y} := induction_on₂ x y fun x y hx hy ↦ by
    simp_rw [Set.mem_ofPred_eq, mk_mul, liftOn_mk, Submonoid.coe_mul] at *
    suffices 0 ≤ x.1 * x.2 * (y.1 * y.2) by grind
    positivity

theorem isPointed_nonneg_priv : (nonneg_priv s).IsPointed :=
  fun x ↦ induction_on x fun x h₁ h₂ ↦ by
    simp only [AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq,
      liftOn_mk, neg_mk] at *
    rw [← mk_zero 1, mk_eq_mk_iff, r_iff_of_nontrivial]
    grind [zero_eq_mul, coe_denom_ne_zero, mk_eq_mk_iff, r_iff_of_nontrivial]

instance : DecidablePred fun x ↦ x ∈ (nonneg_priv s).toAddSubmonoid := fun x ↦
  recOnSubsingleton x (fun a₁ a₂ ↦ decidable_of_iff' (0 ≤ a₁ * a₂) (by simp))

instance : LinearOrder (Localization s) :=
  .mkOfAddSubmonoid (isPointed_nonneg_priv s) fun x ↦ induction_on x fun x ↦ by
    simpa [neg_mk] using le_total ..

instance : IsOrderedRing (Localization s) := .mkOfSubsemiring (isPointed_nonneg_priv s)

@[simp high]
theorem mk_le_mk₀ (a₁ b₁ : R) (a₂ b₂ : s) :
    mk a₁ a₂ ≤ mk b₁ b₂ ↔ a₁ * a₂ * b₂ * b₂ ≤ b₁ * b₂ * a₂ * a₂ := by
  simp [sub_mk]
  grind

@[simp high]
theorem algebraMap_mono (a b : R) :
    algebraMap _ (Localization s) a ≤ algebraMap _ _ b ↔ a ≤ b := by
  simp [← mk_one_eq_algebraMap]

@[mono]
theorem algebraMap_monotone : Monotone (algebraMap R (Localization s)) :=
  fun _ _ ↦ (algebraMap_mono _ _ _).mpr

#synth IsStrictOrderedRing (FractionRing R)

end Localization
