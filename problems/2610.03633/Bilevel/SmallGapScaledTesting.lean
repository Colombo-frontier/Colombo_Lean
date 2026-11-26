import Bilevel.SmallGapScaling
import Bilevel.SmallGapTesting

/-! The concrete finite-horizon lower bound under the manuscript's exact
parameter scaling. All geometric and regularity side conditions are derived
by `SmallGapScaling`, with fixed universal numerical constants. -/

noncomputable section
open MeasureTheory
namespace Bilevel.SmallGapScaling.Input
open SmallGapLiftSupport SmallGapInstance SmallGapTesting

variable (Q : SmallGapScaling.Input)

theorem signal_scale : Q.parameters.signalBound =
    (39296 * C ^ 2) * Q.ε ^ 2 / (Q.κ ^ 3 * Q.L * Q.θ) := by
  dsimp [Parameters.signalBound, parameters]
  field_simp [Q.L_pos.ne', Q.κ_pos.ne', Q.θ_pos.ne']
  ring

theorem noise_scale (σ : ℝ) : σ ^ 2 / Q.parameters.signalBound ^ 2 =
    Q.κ ^ 6 * Q.L ^ 2 * Q.θ ^ 2 * σ ^ 2 / ((39296 * C ^ 2) ^ 2 * Q.ε ^ 4) := by
  rw [Q.signal_scale]
  have hC := C_pos
  field_simp [Q.L_pos.ne', Q.κ_pos.ne', Q.θ_pos.ne', Q.ε_pos.ne']
  ring

variable {State Seed : Type*} [MeasurableSpace State] [MeasurableSpace Seed]

/-- Every actual adaptive execution achieving the target for the two source
signs has this concrete call lower bound. -/
theorem scaled_fixed_horizon_bound (ν : Measure Seed) [IsProbabilityMeasure ν] (σ : ℝ)
    (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (readout : State → ℝ) (hquery : Measurable query)
    (hupdate : Measurable (fun so : State × Observation => update so.1 so.2))
    (hinitial : Measurable initial) (hreadout : Measurable readout) (n : ℕ)
    (accuracy : (risk Q.parameters ν (Q.parameters.activationProbability σ) 1
        (Q.parameters.activationProbability_le_one σ) query update initial readout n +
      risk Q.parameters ν (Q.parameters.activationProbability σ) (-1)
        (Q.parameters.activationProbability_le_one σ) query update initial readout n) / 2 ≤ Q.ε) :
    (7 / 8 : ℝ) * (1 + Q.κ ^ 6 * Q.L ^ 2 * Q.θ ^ 2 * σ ^ 2 /
      ((39296 * C ^ 2) ^ 2 * Q.ε ^ 4)) ≤ (n : ℝ) := by
  have hacc : (risk Q.parameters ν (Q.parameters.activationProbability σ) 1
        (Q.parameters.activationProbability_le_one σ) query update initial readout n +
      risk Q.parameters ν (Q.parameters.activationProbability σ) (-1)
        (Q.parameters.activationProbability_le_one σ) query update initial readout n) / 2 ≤
      ((Q.parameters.L / Q.parameters.μ) * Q.parameters.S * Q.parameters.δ) / 8 := by
    rw [Q.gamma]
    simpa using accuracy
  have h := fixed_horizon_statistical_bound Q.parameters ν σ Q.geometry
    query update initial readout hquery hupdate hinitial hreadout n hacc
  rw [Q.noise_scale σ] at h
  exact h

end Bilevel.SmallGapScaling.Input
