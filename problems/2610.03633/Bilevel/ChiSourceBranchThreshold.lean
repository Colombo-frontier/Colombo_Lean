import Bilevel.ChiExtensionCalibration

/-! A single fixed branch threshold supplies positive depth, the middle
floor scale condition, and T≥2 for the actual source schedule. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiCurvatureSchedule

def sourceBranchThreshold (CT η : ℝ) : ℝ :=
  max (threshold CT 6) (max (Real.exp 4) (6/η))

theorem source_branch_conditions {CT η θ κ : ℝ} (hCT : 1 ≤ CT)
    (hθ : sourceBranchThreshold CT η ≤ θ) (hθκ : θ ≤ κ) :
    1 ≤ θ ∧ 1 ≤ ChiIndependentWidths.chosenDepth θ ∧ 1/η ≤ κ/6 ∧
      threshold CT 6 ≤ θ ∧ 2 ≤ scale θ CT 6 := by
  have hthreshold : threshold CT 6 ≤ θ := (le_max_left _ _).trans hθ
  have hθ1 : 1 ≤ θ := (le_max_left _ _).trans hthreshold
  have hexp : Real.exp 4 ≤ θ := (le_max_left _ _).trans ((le_max_right _ _).trans hθ)
  have hfloor : 6/η ≤ θ := (le_max_right _ _).trans ((le_max_right _ _).trans hθ)
  have hJ : 1 ≤ ChiIndependentWidths.chosenDepth θ := by
    have hu := chosenDepth_upper hθ1
    have hl := Real.log_le_log (Real.exp_pos 4) (show Real.exp 4 ≤ 2+θ by linarith)
    rw [Real.log_exp] at hl
    by_contra hn
    have hz : ChiIndependentWidths.chosenDepth θ=0 := by omega
    rw [hz] at hu
    norm_num at hu
    linarith
  refine ⟨hθ1,hJ,?_,hthreshold,scale_ge_two_above_threshold hCT 6 hthreshold⟩
  have hh := hfloor.trans hθκ
  apply (le_div_iff₀ (by norm_num : (0:ℝ) < 6)).mpr
  convert hh using 1
  ring

end Bilevel.ChiExtensionCalibration
