import UpperGhostOptimization
import UpperGhostMoments
import UpperGhostProgramRisk
import UpperGhostAccuracy

/-! The original sharp ghost expected-error bound for every source-model
instance, including genuine integrability of the ghost output gap. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Metric Set
open scoped NNReal

namespace Task006.Full.SampleInstance
variable {d : ℕ} {L : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] (P : UpperProgramParameters)
  (I : Task006.Full.SampleInstance d L P.R Ω μ)

noncomputable def upperGhostGap (T : ℕ) (j : GhostState (UpperGhostState d)) : ℝ :=
  I.objective ((T : ℝ)⁻¹ • j.1.2.2) - optimalValue I

set_option maxHeartbeats 1000000 in
theorem upperGhost_expected_risk_le {T : ℕ} (hd : 0 < d) (hT : 0 < T)
    (hR : 0 < P.R) (hL : 0 < L) (hρ : 0 < P.ρ) (hb : 0 < P.b)
    (s : ℝ) (hs : 1 ≤ s) (hq : (d : ℝ) * Real.exp (-s) < 1) :
    Integrable (I.upperGhostGap P T) (I.upperGhostLaw P hR.le hL hd s hs hq T) ∧
      (∫ j, I.upperGhostGap P T j ∂I.upperGhostLaw P hR.le hL hd s hs hq T) ≤
        ghostRiskBudget P d L s T := by
  let F := I.rebalancedSample hR.le
  let G := I.upperGhostGood (d := d) (Ω := Ω) P hR.le s
  let ν := upperSampleBlockLaw d μ
  let step := upperGhostStep (d := d) (Ω := Ω) P F
  let π := I.upperGhostLaw P hR.le hL hd s hs hq T
  let f := I.smoothedObjective hL.le hR.le P.ρ
  have hF : Measurable (Function.uncurry F) := I.rebalancedSample_measurable hR.le
  have hstep : Measurable step := upperGhostStep_measurable P hF
  have hG := I.upperGhostGood_measurable P hR.le s
  have hpos := I.upperGhostGood_pos P hR.le hL hd hs hq
  letI : IsProbabilityMeasure π := by
    dsimp only [π, upperGhostLaw]
    infer_instance
  have hfeas : ∀ᵐ j ∂π, upperGhostFeasible P T j :=
    ghostProcess_upperStep_feasible P F hF ν G hG hpos T
  have hρR : P.ρ ≤ P.R := by linarith [P.inner_nonneg, P.delta_pos]
  have hrR : P.R - (P.ρ + P.δ) ≤ P.R := by linarith [P.rho_nonneg, P.delta_pos]
  have hκ : 0 ≤ P.ρ + P.δ := by linarith [P.rho_nonneg, P.delta_pos]
  have hκR : P.ρ + P.δ ≤ P.R := by linarith [P.inner_nonneg]
  obtain ⟨xmin, hxmin, hvalue, _⟩ := I.exists_objective_minimizer hL.le hR.le
  have hxminNorm : ‖xmin‖ ≤ P.R := by simpa only [outputDomain, mem_closedBall, dist_zero_right] using hxmin
  let z := (1 - (P.ρ + P.δ) / P.R) • xmin
  have hshrink := shrink_comparator hR hκ hκR hxminNorm
  have hz : ‖z‖ ≤ P.R - (P.ρ + P.δ) := hshrink.1
  have hfLip : LipschitzWith ⟨L, hL.le⟩ f := I.smoothedObjective_lipschitz hL.le hR.le hρ
  have hregret := goodStateLaw_upper_regret P hT F hF ν G hG hpos f ⟨L, hL.le⟩ hfLip
    (I.smoothedObjective_convex hL.le hR.le hρ.le hρR hrR)
    (I.smoothedGradient hL.le hR.le P.ρ)
    (β := ghostBiasBudget P d L s) (W := ghostSecondBudget P d L s)
    (fun x hx => (I.upperGhost_direction_moments_sharp P hR.le hL hd hρ hb hs hq hx).2.2.1)
    (fun x hx => (I.upperGhost_direction_moments_sharp P hR.le hL hd hρ hb hs hq hx).2.2.2)
    z hz (fun x hx => I.smoothedObjective_gradient_gap hL.le hR.le hρ hρR hrR hx hz)
  have hghost : Measurable (fun j : GhostState (UpperGhostState d) => j.1.2) := measurable_snd.comp measurable_fst
  have hmap : π.map (fun j => j.1.2) = goodStateLaw ν G hG step (0, 0) T :=
    ghostProcess_ghost_marginal ν G hG hpos step hstep (0, 0) T
  have hH : Measurable (fun x : UpperGhostState d => f ((T : ℝ)⁻¹ • x.2) - f z) :=
    (hfLip.continuous.measurable.comp (measurable_snd.const_smul ((T : ℝ)⁻¹))).sub measurable_const
  have hregJoint : (∫ j : GhostState (UpperGhostState d), f ((T : ℝ)⁻¹ • j.1.2.2) - f z ∂π) ≤
      P.R ^ 2 / (2 * P.η * T) + 2 * P.R * ghostBiasBudget P d L s + P.η * ghostSecondBudget P d L s / 2 := by
    have heq := integral_map (μ := π) hghost.aemeasurable hH.aestronglyMeasurable
    rw [hmap] at heq
    rw [heq] at hregret
    exact hregret
  have hLossI : Integrable (fun j : GhostState (UpperGhostState d) => I.upperGhostLoss P hL.le hR.le T j.1.2) π := by
    apply Integrable.of_bound ((I.upperGhostLoss_measurable P hL.le hR.le T).comp hghost).aestronglyMeasurable (2 * L * P.R)
    filter_upwards [] with j
    have hb := I.upperGhostLoss_bounds P hL.le hR.le T j.1.2
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2
  have hLossEq : (fun j : GhostState (UpperGhostState d) => I.upperGhostLoss P hL.le hR.le T j.1.2) =ᵐ[π]
      I.upperGhostGap P T := by
    filter_upwards [hfeas] with j hj
    exact I.upperGhostLoss_eq P hL.le hR.le T j.1.2
      ((upperGhost_average_norm_le P hT hj.2.2.2).trans hrR)
  have hGapI : Integrable (I.upperGhostGap P T) π := hLossI.congr hLossEq
  have hSmoothI : Integrable (fun j : GhostState (UpperGhostState d) => f ((T : ℝ)⁻¹ • j.1.2.2) - f z) π := by
    apply Integrable.of_bound ((hfLip.continuous.measurable.comp
      ((measurable_snd.comp (measurable_snd.comp measurable_fst)).const_smul ((T : ℝ)⁻¹))).sub measurable_const).aestronglyMeasurable
      (2 * L * P.R)
    filter_upwards [hfeas] with j hj
    have hy := upperGhost_average_norm_le P hT hj.2.2.2
    have hn : ‖(T : ℝ)⁻¹ • j.1.2.2 - z‖ ≤ 2 * P.R := by linarith [norm_sub_le ((T : ℝ)⁻¹ • j.1.2.2) z]
    have hb : L * ‖(T : ℝ)⁻¹ • j.1.2.2 - z‖ ≤ 2 * L * P.R := by
      nlinarith [mul_le_mul_of_nonneg_left hn hL.le]
    change ‖f ((T : ℝ)⁻¹ • j.1.2.2) - f z‖ ≤ 2 * L * P.R
    exact (hfLip.norm_sub_le _ _).trans hb
  have hzQuery : z ∈ queryDomain d P.R := by
    change dist z 0 ≤ 2 * P.R
    rw [dist_zero_right]
    linarith
  have hxminQuery : xmin ∈ queryDomain d P.R := by
    change dist xmin 0 ≤ 2 * P.R
    rw [dist_zero_right]
    linarith
  have hcomp : I.objective z - optimalValue I ≤ L * (P.ρ + P.δ) := by
    rw [← hvalue]
    exact (le_abs_self _).trans ((I.objective_lipschitz hL.le hR.le hzQuery hxminQuery).trans
      (mul_le_mul_of_nonneg_left hshrink.2 hL.le))
  have hpoint : ∀ᵐ j ∂π, I.upperGhostGap P T j ≤ f ((T : ℝ)⁻¹ • j.1.2.2) - f z +
      (2 * P.ρ * L + L * (P.ρ + P.δ)) := by
    filter_upwards [hfeas] with j hj
    have hy := upperGhost_average_norm_le P hT hj.2.2.2
    have hey := I.smoothedObjective_error hL.le hR.le P.rho_nonneg hρR (hy.trans hrR)
    have hez := I.smoothedObjective_error hL.le hR.le P.rho_nonneg hρR (hz.trans hrR)
    change |f ((T : ℝ)⁻¹ • j.1.2.2) - I.objective ((T : ℝ)⁻¹ • j.1.2.2)| ≤ P.ρ * L at hey
    change |f z - I.objective z| ≤ P.ρ * L at hez
    change I.objective ((T : ℝ)⁻¹ • j.1.2.2) - optimalValue I ≤ _
    linarith [(abs_le.mp hey).1, (abs_le.mp hez).2]
  refine ⟨hGapI, ?_⟩
  have hm := integral_mono_ae hGapI
    (hSmoothI.add (integrable_const (2 * P.ρ * L + L * (P.ρ + P.δ)))) hpoint
  have hadd := integral_add hSmoothI (integrable_const (2 * P.ρ * L + L * (P.ρ + P.δ)))
  simp only [Pi.add_apply] at hm hadd
  rw [hadd] at hm
  simp only [integral_const, probReal_univ, one_smul] at hm
  exact hm.trans (by unfold ghostRiskBudget; linarith [hregJoint])

#print axioms upperGhost_expected_risk_le
end Task006.Full.SampleInstance
