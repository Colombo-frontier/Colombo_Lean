import GradientHessian.RadialHigherDerivatives
import GradientHessian.LocalizedProductDerivatives

/-! The literal radial cap in the manuscript. Squared-radius coordinates
remove the apparent singularity at the origin without changing the function. -/

namespace GradientHessian.LeafCutoff
open Profiles RadialHigherDerivatives
open Set Filter
open scoped Topology BigOperators InnerProductSpace
noncomputable section

def profile (t : ℝ) : ℝ := 1-step (Real.sqrt t-1)
def radial (L r : ℝ) : ℝ := 1-step (r/L-1)

theorem profile_one {t : ℝ} (ht : t ≤ 1) : profile t = 1 := by
  have hs : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht
  simp [profile, step_nonpos (by linarith : Real.sqrt t-1 ≤ 0)]

theorem profile_contDiff : ContDiff ℝ 3 profile := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  by_cases ht : t < 1
  · apply (contDiffAt_const : ContDiffAt ℝ 3 (fun _ : ℝ => (1:ℝ)) t).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds ht] with u hu
    exact profile_one hu.le
  · have ht0 : 0 < t := by linarith
    exact contDiffAt_const.sub (contDiff_step.contDiffAt.comp t
      ((Real.contDiffAt_sqrt ht0.ne').sub contDiffAt_const))

theorem profile_jet_bound (n : ℕ) (hn : n ≤ 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ i ≤ n, ∀ t ∈ Icc (0:ℝ) 16, |iteratedDeriv i profile t| ≤ C := by
  induction n with
  | zero =>
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (profile_contDiff.continuous.continuousOn : ContinuousOn profile (Icc (0:ℝ) 16))
    refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro i hi t ht
    have hi0 : i = 0 := by omega
    simpa only [hi0, iteratedDeriv_zero, Real.norm_eq_abs] using (hC t ht).trans (le_max_right 1 C)
  | succ n ih =>
    obtain ⟨C, hC, hbound⟩ := ih (by omega)
    obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((profile_contDiff.continuous_iteratedDeriv (n+1) (by exact_mod_cast hn)).continuousOn :
        ContinuousOn (iteratedDeriv (n+1) profile) (Icc (0:ℝ) 16))
    refine ⟨max C D, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
    intro i hi t ht
    by_cases hin : i ≤ n
    · exact (hbound i hin t ht).trans (le_max_left _ _)
    · have he : i = n+1 := by omega
      subst i
      exact (show |iteratedDeriv (n+1) profile t| ≤ D by
        simpa only [Real.norm_eq_abs] using hD t ht).trans (le_max_right _ _)

def profileConstant : ℝ := (profile_jet_bound 3 le_rfl).choose
def cutoffConstant (n : ℕ) : ℝ := n.factorial*profileConstant*32^n

theorem profileConstant_pos : 0 < profileConstant := (profile_jet_bound 3 le_rfl).choose_spec.1
theorem cutoffConstant_pos (n : ℕ) : 0 < cutoffConstant n := by
  have h := profileConstant_pos
  unfold cutoffConstant
  positivity

theorem profileConstant_spec {i : ℕ} (hi : i ≤ 3) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 16) :
    ‖iteratedFDeriv ℝ i profile t‖ ≤ profileConstant := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact (profile_jet_bound 3 le_rfl).choose_spec.2 i hi t ht

theorem radial_bounds (L r : ℝ) : radial L r ∈ Icc (0:ℝ) 1 := by
  have h := step_bounds (r/L-1)
  unfold radial
  constructor <;> linarith [h.1, h.2]

theorem radial_one {L r : ℝ} (hL : 0 < L) (hr : r ≤ L) : radial L r = 1 := by
  have harg : r/L-1 ≤ 0 := by have h := (div_le_one hL).mpr hr; linarith
  simp [radial, step_nonpos harg]

theorem radial_zero {L r : ℝ} (hL : 0 < L) (hr : 2*L ≤ r) : radial L r = 0 := by
  have harg : 1 ≤ r/L-1 := by have h := (le_div_iff₀ hL).mpr hr; linarith
  simp [radial, step_ge_one harg]

theorem radial_derivative (L r : ℝ) :
    HasDerivAt (radial L) (-step₁ (r/L-1)/L) r := by
  convert ((step_derivative (r/L-1)).comp r
    (((hasDerivAt_id r).div_const L).sub_const 1)).const_sub 1 using 1
  ring

theorem radial_derivative_nonpos {L : ℝ} (hL : 0 < L) (r : ℝ) : deriv (radial L) r ≤ 0 := by
  rw [(radial_derivative L r).deriv]
  have h := (derivative_bounds (r/L-1)).1
  rw [deriv_step] at h
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h) hL.le

theorem radial_derivative_bound {L : ℝ} (hL : 0 < L) (r : ℝ) :
    |deriv (radial L) r| ≤ (35/16)/L := by
  rw [(radial_derivative L r).deriv, abs_div, abs_neg, abs_of_pos hL]
  have h := derivative_bounds (r/L-1)
  rw [deriv_step] at h
  rw [abs_of_nonneg h.1]
  exact div_le_div_of_nonneg_right h.2 hL.le

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def cutoff (L : ℝ) (y : E) : ℝ := radial L ‖y‖

omit [InnerProductSpace ℝ E] in
theorem cutoff_bounds (L : ℝ) (y : E) : cutoff L y ∈ Icc (0:ℝ) 1 := radial_bounds _ _
omit [InnerProductSpace ℝ E] in
theorem cutoff_one {L : ℝ} (hL : 0 < L) {y : E} (hy : ‖y‖ ≤ L) : cutoff L y = 1 := radial_one hL hy
omit [InnerProductSpace ℝ E] in
theorem cutoff_zero {L : ℝ} (hL : 0 < L) {y : E} (hy : 2*L ≤ ‖y‖) : cutoff L y = 0 := radial_zero hL hy

theorem cutoff_one_profile (y : E) : cutoff 1 y = profile ⟪y,y⟫_ℝ := by
  simp [cutoff, radial, profile, real_inner_self_eq_norm_sq, Real.sqrt_sq_eq_abs]

theorem cutoff_scaling {L : ℝ} (hL : 0 < L) (y : E) : cutoff L y = cutoff 1 (L⁻¹ • y) := by
  simp [cutoff, radial, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hL, div_eq_mul_inv, mul_comm]

theorem cutoff_one_contDiff : ContDiff ℝ 3 (cutoff 1 : E → ℝ) := by
  rw [show (cutoff 1 : E → ℝ) = fun y => profile ⟪y,y⟫_ℝ from funext cutoff_one_profile]
  exact profile_contDiff.comp (contDiff_id.inner ℝ contDiff_id)

theorem cutoff_contDiff {L : ℝ} (hL : 0 < L) : ContDiff ℝ 3 (cutoff L : E → ℝ) := by
  rw [show (cutoff L : E → ℝ) = fun y => cutoff 1 (L⁻¹ • y) from funext (cutoff_scaling hL)]
  exact cutoff_one_contDiff.comp (contDiff_const.smul contDiff_id)

theorem cutoff_one_derivative_bound (n : ℕ) (hn : n ≤ 3) (y : E) :
    ‖iteratedFDeriv ℝ n (cutoff 1 : E → ℝ) y‖ ≤ cutoffConstant n := by
  by_cases hy : ‖y‖ ≤ 4
  · rw [show (cutoff 1 : E → ℝ) = fun z => profile ⟪z,z⟫_ℝ from funext cutoff_one_profile]
    apply norm_iteratedFDeriv_comp_le profile_contDiff
      (show ContDiff ℝ 3 (fun z : E => ⟪z,z⟫_ℝ) from contDiff_id.inner ℝ contDiff_id)
      (by exact_mod_cast hn) y
    · intro i hi
      apply profileConstant_spec (hi.trans hn)
      rw [real_inner_self_eq_norm_sq]
      exact ⟨sq_nonneg _, by nlinarith [norm_nonneg y]⟩
    · intro i hi _
      exact norm_iteratedFDeriv_inner_self_le hy i hi
  · have he : (cutoff 1 : E → ℝ) =ᶠ[𝓝 y] (fun _ => 0) := by
      have hnear : ∀ᶠ z : E in 𝓝 y, 4 < ‖z‖ :=
        continuous_norm.continuousAt.eventually (lt_mem_nhds (lt_of_not_ge hy))
      filter_upwards [hnear] with z hz
      exact cutoff_zero (by norm_num) (by linarith)
    rw [iteratedFDeriv_eq_of_eventuallyEq he n, iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero]
    exact (cutoffConstant_pos n).le

theorem cutoff_derivative_bound {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : n ≤ 3) (y : E) :
    ‖iteratedFDeriv ℝ n (cutoff L : E → ℝ) y‖ ≤ cutoffConstant n/L^n := by
  let A : E →L[ℝ] E := L⁻¹ • ContinuousLinearMap.id ℝ E
  have hA : ‖A‖ ≤ L⁻¹ := by
    dsimp only [A]
    rw [norm_smul L⁻¹ (ContinuousLinearMap.id ℝ E), Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hL.le) ContinuousLinearMap.norm_id_le
  rw [show (cutoff L : E → ℝ) = cutoff 1 ∘ A from funext (cutoff_scaling hL),
    A.iteratedFDeriv_comp_right cutoff_one_contDiff y (by exact_mod_cast hn)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (cutoff 1 : E → ℝ) (A y)‖*‖A‖^n := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ n (cutoff 1 : E → ℝ) (A y)).norm_compContinuousLinearMap_le (fun _ => A)
    _ ≤ cutoffConstant n*(L⁻¹)^n := mul_le_mul
      (cutoff_one_derivative_bound n hn _) (pow_le_pow_left₀ (norm_nonneg A) hA n)
      (by positivity) (cutoffConstant_pos n).le
    _ = _ := by rw [inv_pow, div_eq_mul_inv]

end
end GradientHessian.LeafCutoff
