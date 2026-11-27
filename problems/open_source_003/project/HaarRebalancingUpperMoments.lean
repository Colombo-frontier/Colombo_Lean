import HaarRebalancingUpperMarginal
import HaarRebalancingBlockIntegration

/-! Actual clipped-estimator bounds under its original Haar/ball/sample block
law. Good/bad integration replaces the ghost sampler in this main-proof route. -/
set_option maxHeartbeats 1000000
open MeasureTheory Set
open Task006.HaarRebalancing
open scoped BigOperators NNReal
namespace Task006.Full
noncomputable section

/-- The actual block direction after fixing only its Haar basis. -/
def upperFixedBasisDirection {d : ℕ} {Ω : Type*} (P : UpperProgramParameters)
    (F : Space d → Ω → ℝ) (x : Space d) (Q : OrthogonalGroup d) (z : UpperRoundNoise d Ω) : Space d :=
  upperBlockDirection (d := d) (Ω := Ω) P F x ((Q,z.1),z.2)

namespace SampleInstance
variable {d : ℕ} {L : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] (P : UpperProgramParameters)
  (I : SampleInstance d L P.R Ω μ)

theorem upperFixedBasisDirection_eq_clippedVector (hR : 0 ≤ P.R) (x : Space d)
    (Q : OrthogonalGroup d) :
    upperFixedBasisDirection P (I.rebalancedSample hR) x Q =
      clippedVector Q P.b (I.upperCoordinateSecant hR P.ρ P.δ x Q) := by
  funext z
  unfold upperFixedBasisDirection upperBlockDirection clippedVector orthogonalReconstruct
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  rw [I.upperCoordinateSecant_eq_formula hR P.ρ P.δ x Q i z]

/-- Norm of the actual population smoothing gradient, derived from the
Lipschitz objective extension and its actual convolution derivative. -/
theorem smoothedGradient_norm_le (hL : 0 ≤ L) (hR : 0 ≤ P.R) (ρ : ℝ) (x : Space d) :
    ‖I.smoothedGradient hL hR ρ x‖ ≤ L := by
  change ‖(InnerProductSpace.toDual ℝ (Space d)).symm
    (ballSmoothDerivative (I.objectiveExtension hL hR) ρ x)‖ ≤ L
  rw [LinearIsometryEquiv.norm_map]
  exact ballSmoothDerivative_norm_le (I.objectiveExtension_lipschitz hL hR) ρ x

theorem rebalancingThreshold_nonneg (L : ℝ) (d : ℕ) (s : ℝ) (hL : 0 ≤ L) (hs : 0 ≤ s) :
    0 ≤ rebalancingThreshold L d s := by
  have hC0 : 0 ≤ Task006.SphereConcentration.thirdHalfMomentConstant :=
    le_trans (by norm_num) Task006.SphereConcentration.thirdHalfMomentConstant_ge_one
  have hK : 0 ≤ rebalancingK0 := Real.rpow_nonneg (by positivity) _
  have hB : 0 ≤ rebalancingB := by unfold rebalancingB; positivity
  have hC : 0 ≤ rebalancingC2 := Real.rpow_nonneg hB _
  exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hL _))
    (Real.rpow_nonneg (div_nonneg hs (Nat.cast_nonneg d)) _)

/-- Every fixed actual Haar basis has integrable clipped direction and squared
norm. On good bases the precise scalar-clipping bias and second moment hold. -/
theorem upperFixedBasisDirection_good_moments (hR : 0 ≤ P.R) (hL : 0 < L)
    (hd : 0 < d) (hρ : 0 < P.ρ) (hb : 0 < P.b)
    {s : ℝ} (hs : 1 ≤ s) {x : Space d} (hx : ‖x‖ ≤ P.R - (P.ρ + P.δ))
    (Q : OrthogonalGroup d) (hQ : I.goodRebalancedBasis hR P.ρ P.δ s x Q) :
    Integrable (upperFixedBasisDirection P (I.rebalancedSample hR) x Q) (upperRoundNoiseLaw d μ) ∧
    Integrable (fun z => ‖upperFixedBasisDirection P (I.rebalancedSample hR) x Q z‖ ^ 2)
      (upperRoundNoiseLaw d μ) ∧
    ‖(∫ z, upperFixedBasisDirection P (I.rebalancedSample hR) x Q z ∂upperRoundNoiseLaw d μ) -
      I.smoothedGradient hL.le hR P.ρ x‖ ≤
      Real.sqrt d * rebalancingThreshold L d s * P.b ^ (-1 / 2 : ℝ) +
        Real.sqrt d * (d * L * P.δ / P.ρ) ∧
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
    (a := d * L * P.δ / P.ρ) (div_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hL.le) P.delta_pos.le) hρ.le) (by
      intro i
      rw [hmean i, real_inner_comm]
      exact I.centralSecant_smoothedGradient_error hL.le hR hρ hρR P.delta_pos
        (by omega) hx ((orthonormal_column Q).norm_eq_one i).le)
  refine ⟨hc.1, hc.2.1, ?_, hc.2.2.2⟩
  calc
    _ ≤ ‖(∫ z, clippedVector Q P.b D z ∂upperRoundNoiseLaw d μ) -
          orthogonalReconstruct Q (fun i => ∫ z, D i z ∂upperRoundNoiseLaw d μ)‖ +
        ‖orthogonalReconstruct Q (fun i => ∫ z, D i z ∂upperRoundNoiseLaw d μ) -
          I.smoothedGradient hL.le hR P.ρ x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add hc.2.2.1 hbias

/-- Actual one-round estimator bounds under the implemented block law. Every
quantity is derived from the original sample instance and actual U3; no terminal
vector-moment, conditional-law or good-basis probability is a hypothesis. -/
theorem upperBlockDirection_moments (hR : 0 ≤ P.R) (hL : 0 < L)
    (hd : 0 < d) (hρ : 0 < P.ρ) (hb : 0 < P.b)
    {s : ℝ} (hs : 1 ≤ s) {x : Space d} (hx : ‖x‖ ≤ P.R - (P.ρ + P.δ)) :
    Integrable (upperBlockDirection (d := d) (Ω := Ω) P (I.rebalancedSample hR) x) (upperSampleBlockLaw d μ) ∧
    Integrable (fun block => ‖upperBlockDirection (d := d) (Ω := Ω) P (I.rebalancedSample hR) x block‖ ^ 2)
      (upperSampleBlockLaw d μ) ∧
    ‖(∫ block, upperBlockDirection (d := d) (Ω := Ω) P (I.rebalancedSample hR) x block ∂upperSampleBlockLaw d μ) -
      I.smoothedGradient hL.le hR P.ρ x‖ ≤
      Real.sqrt d * rebalancingThreshold L d s * P.b ^ (-1 / 2 : ℝ) +
        Real.sqrt d * (d * L * P.δ / P.ρ) +
          (Real.sqrt d * P.b + L) * ((d : ℝ) * Real.exp (-s)) ∧
    (∫ block, ‖upperBlockDirection (d := d) (Ω := Ω) P (I.rebalancedSample hR) x block‖ ^ 2
      ∂upperSampleBlockLaw d μ) ≤
      d * rebalancingThreshold L d s * P.b ^ (1 / 2 : ℝ) +
        (d * P.b ^ 2) * ((d : ℝ) * Real.exp (-s)) := by
  let G : Set (OrthogonalGroup d) := {Q | I.goodRebalancedBasis hR P.ρ P.δ s x Q}
  have hG : MeasurableSet G := measurable_prodMk_left (x := x)
    (I.measurableSet_goodRebalancedBasis hR P.ρ P.δ s)
  have hbad : (orthogonalHaarProbability d).real Gᶜ ≤ (d : ℝ) * Real.exp (-s) :=
    I.badRebalancedBasis_probability_le hR hd hL P.delta_pos hs x
  have hF : Measurable (Function.uncurry (I.rebalancedSample hR)) :=
    I.rebalancedSample_measurable hR
  have hM := rebalancingThreshold_nonneg L d s hL.le (by linarith)
  have hfd : 0 ≤ (d : ℝ) * L * P.δ / P.ρ := div_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hL.le) P.delta_pos.le) hρ.le
  have hgood := I.upperFixedBasisDirection_good_moments P hR hL hd hρ hb hs hx
  exact upperBlockDirection_mixture P hF x (I.smoothedGradient hL.le hR P.ρ x) G hG
    (a := Real.sqrt d * rebalancingThreshold L d s * P.b ^ (-1 / 2 : ℝ) +
      Real.sqrt d * ((d : ℝ) * L * P.δ / P.ρ))
    (v := (d : ℝ) * rebalancingThreshold L d s * P.b ^ (1 / 2 : ℝ))
    (l := L) (q := (d : ℝ) * Real.exp (-s))
    (by positivity) (by positivity) hL.le (I.smoothedGradient_norm_le P hL.le hR P.ρ x)
    hbad (fun Q hQ => (hgood Q hQ).2.2.1) (fun Q hQ => (hgood Q hQ).2.2.2)

end SampleInstance
end
end Task006.Full
