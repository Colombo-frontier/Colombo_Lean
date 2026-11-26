import SphereSmoothingSharp
import HaarRebalancingUpperMoments

/-! The exact source good-basis bounds, retaining U2's one-half factor. -/
set_option maxHeartbeats 1000000
open MeasureTheory Set
open Task006.HaarRebalancing
open scoped BigOperators NNReal
namespace Task006.Full.SampleInstance
noncomputable section
variable {d : ℕ} {L : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] (P : UpperProgramParameters)
  (I : SampleInstance d L P.R Ω μ)

theorem upperFixedBasisDirection_good_moments_sharp (hR : 0 ≤ P.R) (hL : 0 < L)
    (hd : 0 < d) (hρ : 0 < P.ρ) (hb : 0 < P.b)
    {s : ℝ} (hs : 1 ≤ s) {x : Space d} (hx : ‖x‖ ≤ P.R - (P.ρ + P.δ))
    (Q : OrthogonalGroup d) (hQ : I.goodRebalancedBasis hR P.ρ P.δ s x Q) :
    Integrable (upperFixedBasisDirection P (I.rebalancedSample hR) x Q) (upperRoundNoiseLaw d μ) ∧
    Integrable (fun z => ‖upperFixedBasisDirection P (I.rebalancedSample hR) x Q z‖ ^ 2)
      (upperRoundNoiseLaw d μ) ∧
    ‖(∫ z, upperFixedBasisDirection P (I.rebalancedSample hR) x Q z ∂upperRoundNoiseLaw d μ) -
      I.smoothedGradient hL.le hR P.ρ x‖ ≤
      Real.sqrt d * rebalancingThreshold L d s * P.b ^ (-1 / 2 : ℝ) +
        Real.sqrt d * (d * L * P.δ / (2 * P.ρ)) ∧
    (∫ z, ‖upperFixedBasisDirection P (I.rebalancedSample hR) x Q z‖ ^ 2 ∂upperRoundNoiseLaw d μ) ≤
      d * rebalancingThreshold L d s * P.b ^ (1 / 2 : ℝ) := by
  have hρR : P.ρ ≤ P.R := by linarith [P.inner_nonneg, P.delta_pos]
  have hxδ : ‖x‖ + P.δ ≤ P.R := by linarith
  let D := I.upperCoordinateSecant hR P.ρ P.δ x Q
  have hDi := I.upperCoordinateSecant_integrable hR (ρ := P.ρ) P.delta_pos x Q
  have hm (i : Fin d) : (∫ z, |D i z| ^ (3 / 2 : ℝ) ∂upperRoundNoiseLaw d μ) ≤
      rebalancingThreshold L d s := by
    rw [I.upperCoordinateSecant_moment_eq hR P.delta_pos x Q i]
    exact (hQ i).le
  have hc := clippedVector_moments Q hb (rebalancingThreshold_nonneg L d s hL.le (by linarith)) D
    (I.upperCoordinateSecant_measurable hR P.ρ P.δ x Q) (fun i => (hDi i).1) (fun i => (hDi i).2) hm
  have heq := I.upperFixedBasisDirection_eq_clippedVector P hR x Q
  rw [heq]
  have hmean (i : Fin d) : (∫ z, D i z ∂upperRoundNoiseLaw d μ) =
      centralSecant (ballSmooth I.objective P.ρ) x (column Q i) P.δ :=
    I.upperCoordinateSecant_mean_eq hR hL.le P.rho_nonneg hρR P.delta_pos hxδ Q i
  have hbias := orthogonalReconstruct_error hd Q
    (fun i => ∫ z, D i z ∂upperRoundNoiseLaw d μ) (I.smoothedGradient hL.le hR P.ρ x)
    (a := d * L * P.δ / (2 * P.ρ)) (div_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hL.le) P.delta_pos.le) (by positivity)) (by
      intro i
      rw [hmean i, real_inner_comm]
      exact I.centralSecant_smoothedGradient_error_sharp hL.le hR hρ hρR P.delta_pos
        (by omega) hx ((orthonormal_column Q).norm_eq_one i).le)
  refine ⟨hc.1, hc.2.1, ?_, hc.2.2.2⟩
  calc
    _ ≤ ‖(∫ z, clippedVector Q P.b D z ∂upperRoundNoiseLaw d μ) -
          orthogonalReconstruct Q (fun i => ∫ z, D i z ∂upperRoundNoiseLaw d μ)‖ +
        ‖orthogonalReconstruct Q (fun i => ∫ z, D i z ∂upperRoundNoiseLaw d μ) -
          I.smoothedGradient hL.le hR P.ρ x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add hc.2.2.1 hbias


end
end Task006.Full.SampleInstance
