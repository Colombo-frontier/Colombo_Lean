import FullJet.Gate
import Mathlib.Analysis.Normed.Group.Bounded

open scoped ContDiff
open Set

namespace FullJet

theorem gate_derivative_zero_on_upper_plateau {a b t : ℝ}
    (hab : a < b) (ht : b ≤ t) (k : ℕ) (hk : 1 ≤ k) :
    iteratedFDeriv ℝ k (gate a b) t = 0 := by
  have hg : ContDiffAt ℝ k (gate a b) t := (gate_contDiff a b).contDiffAt.of_le (by
    exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Ici b) hg ht]
  rw [iteratedFDerivWithin_congr (𝕜 := ℝ) (s := Ici b) (f := fun _ : ℝ => (1 : ℝ))
    (fun s hs => gate_one hab hs) ht k]
  simp [iteratedFDerivWithin_const_of_ne (by omega : k ≠ 0)]

/-- For each order all gate derivatives are globally bounded. -/
theorem gate_derivative_bounded {a b : ℝ} (hab : a < b) (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t, ‖iteratedFDeriv ℝ k (gate a b) t‖ ≤ C := by
  by_cases hk : k = 0
  · subst k
    refine ⟨1, le_rfl, fun t => ?_⟩
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (gate_range a b t).1]
    exact (gate_range a b t).2
  · have hc := (gate_contDiff a b).continuous_iteratedFDeriv (m := k) (by
      exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc a b) hc.continuousOn
    refine ⟨max 1 C, le_max_left _ _, fun t => ?_⟩
    rcases le_total t a with hta | hat
    · rw [gate_flat hab hta k, norm_zero]
      exact le_trans zero_le_one (le_max_left _ _)
    · rcases le_total b t with hbt | htb
      · rw [gate_derivative_zero_on_upper_plateau hab hbt k (by omega), norm_zero]
        exact le_trans zero_le_one (le_max_left _ _)
      · exact (hC t ⟨hat, htb⟩).trans (le_max_right _ _)

noncomputable def gateDerivativeBound (k : ℕ) : ℝ :=
  Classical.choose (gate_derivative_bounded (a := 5 / 32) (b := 9 / 32) (by norm_num) k)

theorem gateDerivativeBound_ge_one (k : ℕ) : 1 ≤ gateDerivativeBound k :=
  (Classical.choose_spec (gate_derivative_bounded (a := 5 / 32) (b := 9 / 32) (by norm_num) k)).1

theorem explicit_gate_derivative_bound (k : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ k (gate (5 / 32) (9 / 32)) t‖ ≤ gateDerivativeBound k :=
  (Classical.choose_spec (gate_derivative_bounded (a := 5 / 32) (b := 9 / 32) (by norm_num) k)).2 t

theorem expNegInvGlue_monotone : Monotone expNegInvGlue := by
  intro x y hxy
  by_cases hx : x ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos hx]
    exact expNegInvGlue.nonneg y
  · have hx0 : 0 < x := lt_of_not_ge hx
    have hy0 : 0 < y := hx0.trans_le hxy
    simp only [expNegInvGlue, if_neg hx, if_neg hy0.not_le]
    apply Real.exp_le_exp.mpr
    have h := (one_div_le_one_div_of_le hx0 hxy)
    simpa only [one_div] using neg_le_neg h

theorem smoothTransition_monotone : Monotone Real.smoothTransition := by
  intro x y hxy
  unfold Real.smoothTransition
  apply (div_le_div_iff₀ (Real.smoothTransition.pos_denom x)
    (Real.smoothTransition.pos_denom y)).mpr
  have hA := expNegInvGlue_monotone hxy
  have hB := expNegInvGlue_monotone (show 1 - y ≤ 1 - x by linarith)
  have hprod := mul_le_mul hA hB (expNegInvGlue.nonneg (1 - y)) (expNegInvGlue.nonneg y)
  nlinarith

theorem gate_monotone {a b : ℝ} (hab : a < b) : Monotone (gate a b) := by
  intro x y hxy
  exact smoothTransition_monotone (div_le_div_of_nonneg_right
    (sub_le_sub_right hxy a) (sub_pos.mpr hab).le)

end FullJet
