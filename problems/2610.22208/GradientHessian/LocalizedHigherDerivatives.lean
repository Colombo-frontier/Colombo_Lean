import GradientHessian.RadialHigherDerivatives
import GradientHessian.Localized

/-! Dimension-independent tensor estimates for the literal localized profiles.
All constants are chosen from fixed scalar functions before the ambient space.
-/

noncomputable section
open Set Filter
open scoped Topology BigOperators InnerProductSpace

namespace GradientHessian.LocalizedHigherDerivatives
open RadialHigherDerivatives Localized

def scalarCutoff (a b t : ℝ) : ℝ := 1 - Profiles.step ((t-a)/b)

theorem scalarCutoff_contDiff (a b : ℝ) : ContDiff ℝ 3 (scalarCutoff a b) :=
  contDiff_const.sub (Profiles.contDiff_step.comp ((contDiff_id.sub contDiff_const).div_const b))

theorem scalarCutoff_jet_bound (a b : ℝ) (n : ℕ) (hn : n ≤ 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ i ≤ n, ∀ t ∈ Icc (0:ℝ) 16,
      |iteratedDeriv i (scalarCutoff a b) t| ≤ C := by
  induction n with
  | zero =>
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((scalarCutoff_contDiff a b).continuous.continuousOn :
        ContinuousOn (scalarCutoff a b) (Icc (0:ℝ) 16))
    refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro i hi t ht
    have hi₀ : i = 0 := by omega
    simpa only [hi₀, iteratedDeriv_zero, Real.norm_eq_abs] using
      (hC t ht).trans (le_max_right 1 C)
  | succ n ih =>
    obtain ⟨C, hC, hbound⟩ := ih (by omega)
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (((scalarCutoff_contDiff a b).continuous_iteratedDeriv (n+1)
        (by exact_mod_cast hn)).continuousOn :
          ContinuousOn (iteratedDeriv (n+1) (scalarCutoff a b)) (Icc (0:ℝ) 16))
    refine ⟨max C M, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
    intro i hi t ht
    by_cases hin : i ≤ n
    · exact (hbound i hin t ht).trans (le_max_left _ _)
    · have heq : i = n+1 := by omega
      subst i
      exact (show |iteratedDeriv (n+1) (scalarCutoff a b) t| ≤ M by
        simpa only [Real.norm_eq_abs] using hM t ht).trans (le_max_right _ _)

def cutoffJetBound (a b : ℝ) : ℝ := (scalarCutoff_jet_bound a b 3 le_rfl).choose
def cutoffConstant (a b : ℝ) (n : ℕ) : ℝ := n.factorial * cutoffJetBound a b * 32^n

theorem cutoffJetBound_pos (a b : ℝ) : 0 < cutoffJetBound a b :=
  (scalarCutoff_jet_bound a b 3 le_rfl).choose_spec.1

theorem cutoffConstant_pos (a b : ℝ) (n : ℕ) : 0 < cutoffConstant a b n := by
  have h := cutoffJetBound_pos a b
  unfold cutoffConstant
  positivity

theorem cutoffJetBound_spec (a b : ℝ) {i : ℕ} (hi : i ≤ 3) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 16) :
    ‖iteratedFDeriv ℝ i (scalarCutoff a b) t‖ ≤ cutoffJetBound a b := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact (scalarCutoff_jet_bound a b 3 le_rfl).choose_spec.2 i hi t ht

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def unitCutoff (a b : ℝ) (x : E) : ℝ := scalarCutoff a b ⟪x,x⟫_ℝ

theorem unitCutoff_contDiff (a b : ℝ) : ContDiff ℝ 3 (unitCutoff a b : E → ℝ) :=
  (scalarCutoff_contDiff a b).comp (contDiff_id.inner ℝ contDiff_id)

theorem unitCutoff_zero {a b : ℝ} (hb : 0 < b) (hab : a+b ≤ 16) {x : E}
    (hx : 4 ≤ ‖x‖) : unitCutoff a b x = 0 := by
  have harg : 1 ≤ (⟪x,x⟫_ℝ-a)/b := by
    rw [le_div_iff₀ hb, real_inner_self_eq_norm_sq]
    nlinarith [norm_nonneg x]
  simp [unitCutoff, scalarCutoff, Profiles.step_ge_one harg]

theorem unitCutoff_derivative_bound {a b : ℝ} (hb : 0 < b) (hab : a+b ≤ 16)
    (n : ℕ) (hn : n ≤ 3) (x : E) :
    ‖iteratedFDeriv ℝ n (unitCutoff a b : E → ℝ) x‖ ≤ cutoffConstant a b n := by
  by_cases hx : ‖x‖ ≤ 4
  · apply norm_iteratedFDeriv_comp_le (scalarCutoff_contDiff a b)
      (show ContDiff ℝ 3 (fun y : E => ⟪y,y⟫_ℝ) from contDiff_id.inner ℝ contDiff_id)
      (by exact_mod_cast hn) x
    · intro i hi
      apply cutoffJetBound_spec a b (hi.trans hn)
      rw [real_inner_self_eq_norm_sq]
      exact ⟨sq_nonneg _, by nlinarith [norm_nonneg x]⟩
    · intro i hi _
      exact norm_iteratedFDeriv_inner_self_le hx i hi
  · have heq : (unitCutoff a b : E → ℝ) =ᶠ[𝓝 x] (fun _ => 0) := by
      have he : ∀ᶠ y : E in 𝓝 x, 4 < ‖y‖ :=
        continuous_norm.continuousAt.eventually (lt_mem_nhds (lt_of_not_ge hx))
      filter_upwards [he] with y hy
      exact unitCutoff_zero hb hab hy.le
    rw [iteratedFDeriv_eq_of_eventuallyEq heq n, iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero]
    exact (cutoffConstant_pos a b n).le

def scaledCutoff (a b w : ℝ) (c u : E) : ℝ := unitCutoff a b (w⁻¹ • (u-c))

theorem scaledCutoff_derivative_bound {a b w : ℝ} (hb : 0 < b) (hab : a+b ≤ 16)
    (hw : 0 < w) (n : ℕ) (hn : n ≤ 3) (c u : E) :
    ‖iteratedFDeriv ℝ n (scaledCutoff a b w c) u‖ ≤ cutoffConstant a b n / w^n := by
  let A : E →L[ℝ] E := w⁻¹ • ContinuousLinearMap.id ℝ E
  have hA : ‖A‖ ≤ w⁻¹ := by
    dsimp only [A]
    rw [norm_smul w⁻¹ (ContinuousLinearMap.id ℝ E), Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hw.le) ContinuousLinearMap.norm_id_le
  change ‖iteratedFDeriv ℝ n (fun x => (unitCutoff a b ∘ A) (x-c)) u‖ ≤ _
  rw [iteratedFDeriv_comp_sub,
    A.iteratedFDeriv_comp_right (unitCutoff_contDiff a b) (u-c) (by exact_mod_cast hn)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (unitCutoff a b : E → ℝ) (A (u-c))‖ * ‖A‖^n := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ n (unitCutoff a b : E → ℝ) (A (u-c))).norm_compContinuousLinearMap_le (fun _ => A)
    _ ≤ cutoffConstant a b n * (w⁻¹)^n := mul_le_mul
      (unitCutoff_derivative_bound hb hab n hn _) (pow_le_pow_left₀ (norm_nonneg A) hA n)
      (by positivity) (cutoffConstant_pos a b n).le
    _ = cutoffConstant a b n / w^n := by rw [inv_pow, div_eq_mul_inv]

theorem port_eq_scaledCutoff {w : ℝ} (hw : 0 < w) (c u : E) :
    port w c u = scaledCutoff 1 3 w c u := by
  unfold port scaledCutoff unitCutoff scalarCutoff
  rw [real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hw]
  congr 2
  field_simp
  ring_nf
  simp

theorem cutoff_eq_scaledCutoff {w : ℝ} (hw : 0 < w) (c u : E) :
    cutoff w c u = scaledCutoff 4 5 w c u := by
  unfold cutoff scaledCutoff unitCutoff scalarCutoff
  rw [real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hw]
  congr 2
  field_simp
  ring

theorem port_higher_derivative_bound {w : ℝ} (hw : 0 < w) (n : ℕ) (hn : n ≤ 3) (c u : E) :
    ‖iteratedFDeriv ℝ n (port w c) u‖ ≤ cutoffConstant 1 3 n / w^n := by
  rw [show port w c = scaledCutoff 1 3 w c from funext (port_eq_scaledCutoff hw c)]
  exact scaledCutoff_derivative_bound (by norm_num) (by norm_num) hw n hn c u

theorem cutoff_higher_derivative_bound {w : ℝ} (hw : 0 < w) (n : ℕ) (hn : n ≤ 3) (c u : E) :
    ‖iteratedFDeriv ℝ n (cutoff w c) u‖ ≤ cutoffConstant 4 5 n / w^n := by
  rw [show cutoff w c = scaledCutoff 4 5 w c from funext (cutoff_eq_scaledCutoff hw c)]
  exact scaledCutoff_derivative_bound (by norm_num) (by norm_num) hw n hn c u

end GradientHessian.LocalizedHigherDerivatives
