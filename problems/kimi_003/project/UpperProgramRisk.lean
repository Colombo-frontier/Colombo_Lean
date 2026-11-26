import UpperProgramRegret
import UpperProgramBudgets
import UpperSmoothingGlobal
import HaarRebalancingUpperMoments

/-! Actual-instance upper risk from the actual clipped algorithm, with the
conservative `2d L / rho` smoothing derivation and direct Haar mixture. -/

open MeasureTheory MeasureTheory.Measure Metric Set
open Task006.HaarRebalancing
open scoped NNReal

namespace Task006.Full


namespace SampleInstance

set_option maxHeartbeats 3000000 in
theorem upperProgram_risk_le {d T : ℕ} (P : UpperProgramParameters) (hd : 0 < d) (hT : 0 < T)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {L : ℝ}
    (I : SampleInstance d L P.R Ω μ) (hR : 0 < P.R) (hL : 0 < L)
    (hρ : 0 < P.ρ) (hb : 0 < P.b) {s : ℝ} (hs : 1 ≤ s) :
    (∫ w, (upperPairedProgram P hd).toAlgorithm.realizedGap I w
      ∂(upperSeedLaw d T).prod (iidHandleLaw μ)) ≤
      P.R ^ 2 / (2 * P.η * T) + 2 * P.R * upperActualBias P d L s +
        P.η * upperActualSecondMoment P d L s / 2 + 2 * P.ρ * L + L * (P.ρ + P.δ) := by
  let F := I.rebalancedSample hR.le
  let f := I.smoothedObjective hL.le hR.le P.ρ
  let ν := upperSampleBlockLaw d μ
  let π := Measure.pi (fun _ : Fin T => ν)
  have hρR : P.ρ ≤ P.R := by linarith [P.inner_nonneg, P.delta_pos]
  have hrR : P.R - (P.ρ + P.δ) ≤ P.R := by linarith [P.rho_nonneg, P.delta_pos]
  have hκ : 0 ≤ P.ρ + P.δ := by linarith [P.rho_nonneg, P.delta_pos]
  have hκR : P.ρ + P.δ ≤ P.R := by linarith [P.inner_nonneg]
  obtain ⟨xmin, hxmin, hvalue, _⟩ := I.exists_objective_minimizer hL.le hR.le
  have hxminNorm : ‖xmin‖ ≤ P.R := by simpa only [outputDomain, mem_closedBall, dist_zero_right] using hxmin
  let z := (1 - (P.ρ + P.δ) / P.R) • xmin
  have hshrink := shrink_comparator hR hκ hκR hxminNorm
  have hz : ‖z‖ ≤ P.R - (P.ρ + P.δ) := hshrink.1
  have hF : Measurable (Function.uncurry F) := I.rebalancedSample_measurable hR.le
  have hfLip : LipschitzWith ⟨L, hL.le⟩ f := I.smoothedObjective_lipschitz hL.le hR.le hρ
  have hround (x : Space d) (hx : ‖x‖ ≤ P.R - (P.ρ + P.δ)) :=
    I.upperBlockDirection_moments P hR.le hL hd hρ hb hs hx
  have hregret := upperBlock_regret (d := d) (T := T) (Ω := Ω) P hT F hF f ⟨L, hL.le⟩ hfLip
    (I.smoothedObjective_convex hL.le hR.le hρ.le hρR hrR)
    (I.smoothedGradient hL.le hR.le P.ρ)
    (β := upperActualBias P d L s) (W := upperActualSecondMoment P d L s)
    (fun x hx => (hround x hx).1) (fun x hx => (hround x hx).2.2.1)
    (fun x hx => (hround x hx).2.2.2) z hz
    (fun x hx => I.smoothedObjective_gradient_gap hL.le hR.le hρ hρR hrR hx hz)
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
  have hgapInt : Integrable (fun blocks => f (upperBlockOutput (d := d) (T := T) (Ω := Ω) P F blocks) - f z) π := by
    apply Integrable.of_bound ((hfLip.continuous.measurable.comp
      (upperBlockOutput_measurable P hF)).sub measurable_const).aestronglyMeasurable (2 * L * P.R)
    filter_upwards [] with blocks
    have hy := upperBlockOutput_norm_le P hT F blocks
    have hn : ‖upperBlockOutput (d := d) (T := T) (Ω := Ω) P F blocks - z‖ ≤ 2 * P.R := by
      linarith [norm_sub_le (upperBlockOutput (d := d) (T := T) (Ω := Ω) P F blocks) z]
    have hh : (L : ℝ) * ‖upperBlockOutput (d := d) (T := T) (Ω := Ω) P F blocks - z‖ ≤ 2 * L * P.R := by
      nlinarith [mul_le_mul_of_nonneg_left hn hL.le]
    exact (hfLip.norm_sub_le _ _).trans hh
  have hpoint (blocks : Fin T → UpperSampleBlock d Ω) :
      I.objective (upperBlockOutput (d := d) (T := T) (Ω := Ω) P F blocks) - optimalValue I ≤
        f (upperBlockOutput (d := d) (T := T) (Ω := Ω) P F blocks) - f z + (2 * P.ρ * L + L * (P.ρ + P.δ)) := by
    have hy := upperBlockOutput_norm_le P hT F blocks
    have hyR := hy.trans hrR
    have hey := I.smoothedObjective_error hL.le hR.le P.rho_nonneg hρR hyR
    have hez := I.smoothedObjective_error hL.le hR.le P.rho_nonneg hρR (hz.trans hrR)
    change |f (upperBlockOutput (d := d) (T := T) (Ω := Ω) P F blocks) - I.objective (upperBlockOutput (d := d) (T := T) (Ω := Ω) P F blocks)| ≤ P.ρ * L at hey
    change |f z - I.objective z| ≤ P.ρ * L at hez
    have hyL := (abs_le.mp hey).1
    have hzU := (abs_le.mp hez).2
    linarith
  have hnneg : ∀ᵐ blocks ∂π, 0 ≤ I.objective (upperBlockOutput (d := d) (T := T) (Ω := Ω) P F blocks) - optimalValue I := by
    filter_upwards [] with blocks
    have hy := upperBlockOutput_norm_le P hT F blocks
    exact (I.objective_gap_bounds hL.le hR.le (by
      change dist _ 0 ≤ P.R
      rw [dist_zero_right]
      exact hy.trans hrR)).1
  have hm := integral_mono_of_nonneg hnneg
    (hgapInt.add (integrable_const (2 * P.ρ * L + L * (P.ρ + P.δ)))) (ae_of_all _ hpoint)
  have hadd := integral_add hgapInt (integrable_const (2 * P.ρ * L + L * (P.ρ + P.δ)))
  simp only [Pi.add_apply] at hm hadd
  rw [hadd] at hm
  simp only [integral_const, probReal_univ, one_smul] at hm
  rw [I.upperProgram_risk_eq_block_risk P hd hT hL.le hR.le]
  exact hm.trans (by linarith [hregret])

end SampleInstance

#print axioms SampleInstance.upperProgram_risk_le

end Task006.Full
