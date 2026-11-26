import FreshGradientMinimax.OuterRefinement
import FreshGradientMinimax.MainStatements

/-! Dimensionless quantities in the outer rate. The logarithmic envelope
does not contain the dual-localization parameter G. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax

def outerGapRatio (p : Parameters) : ℝ := p.L * p.gap / p.ε ^ 2
def outerColdLog (p : Parameters) : ℝ :=
  Real.log (2 + p.κ ^ 2 * p.G ^ 2 / p.ε ^ 2 + p.κ ^ 2 * outerGapRatio p)

theorem parameter_L_pos (p : Parameters) : 0 < p.L := p.μ_pos.trans_le p.μ_le_L

theorem outerGapRatio_nonneg (p : Parameters) : 0 ≤ outerGapRatio p :=
  div_nonneg (mul_nonneg (parameter_L_pos p).le p.gap_nonneg) (sq_nonneg _)

theorem outerGapRatio_one (p : Parameters) (hreg : p.ε ^ 2 ≤ p.L * p.gap) : 1 ≤ outerGapRatio p := by
  exact (le_div_iff₀ (sq_pos_of_pos p.ε_pos)).mpr (by simpa using hreg)

theorem logarithmicEnvelope_bounds (p : Parameters) :
    1 ≤ logarithmicEnvelope p ∧ Real.log (2 + p.κ) ≤ logarithmicEnvelope p ∧
    Real.log (2 + outerGapRatio p) ≤ logarithmicEnvelope p ∧
    Real.log (2 + p.testing) ≤ logarithmicEnvelope p := by
  have hκ := p.condition_ge_one
  have hA := outerGapRatio_nonneg p
  have hU : 0 ≤ p.testing := by unfold Parameters.testing; positivity
  have h1 : 0 ≤ Real.log (2 + p.κ) := Real.log_nonneg (by linarith)
  have h2 : 0 ≤ Real.log (2 + outerGapRatio p) := Real.log_nonneg (by linarith)
  have h3 : 0 ≤ Real.log (2 + p.testing) := Real.log_nonneg (by linarith)
  have he : logarithmicEnvelope p =
      1 + Real.log (2 + p.κ) + Real.log (2 + outerGapRatio p) + Real.log (2 + p.testing) := rfl
  rw [he]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem outerColdLog_half (p : Parameters) : (1 / 2 : ℝ) ≤ outerColdLog p := by
  have hA := outerGapRatio_nonneg p
  apply log_two_bounds.1.trans
  apply Real.log_le_log (by norm_num : (0 : ℝ) < 2)
  have hG : 0 ≤ p.κ ^ 2 * p.G ^ 2 / p.ε ^ 2 := by positivity
  have hD : 0 ≤ p.κ ^ 2 * outerGapRatio p := by positivity
  change 2 ≤ 2 + p.κ ^ 2 * p.G ^ 2 / p.ε ^ 2 + p.κ ^ 2 * outerGapRatio p
  linarith

theorem outer_deterministic_identity (p : Parameters) : p.deterministic = Real.sqrt p.κ * outerGapRatio p := by
  unfold Parameters.deterministic outerGapRatio
  ring

theorem outer_stochastic_identity (p : Parameters) :
    p.stochastic = outerGapRatio p * (p.κ * p.σ ^ 2 / p.ε ^ 2) := by
  unfold Parameters.stochastic outerGapRatio
  ring

theorem upperRate_identity (p : Parameters) :
    upperRate p = p.deterministic + p.stochastic + p.testing + Real.sqrt p.κ * outerColdLog p := by
  unfold upperRate outerColdLog outerGapRatio
  congr 3
  ring

theorem upperRate_components (p : Parameters) :
    0 ≤ p.deterministic ∧ 0 ≤ p.stochastic ∧ 0 ≤ p.testing ∧ 0 ≤ Real.sqrt p.κ * outerColdLog p := by
  have hL := parameter_L_pos p
  have hΔ := p.gap_nonneg
  have hI := outerColdLog_half p
  have hκ : 0 ≤ p.κ := by linarith [p.condition_ge_one]
  refine ⟨?_, ?_, ?_, mul_nonneg (Real.sqrt_nonneg _) (by linarith)⟩
  · unfold Parameters.deterministic; positivity
  · unfold Parameters.stochastic; positivity
  · unfold Parameters.testing; positivity

theorem upperRate_one (p : Parameters) (hreg : p.ε ^ 2 ≤ p.L * p.gap) : 1 ≤ upperRate p := by
  have ha := outerGapRatio_one p hreg
  have hr : 1 ≤ Real.sqrt p.κ := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt p.condition_ge_one
  have hc := upperRate_components p
  have hd : 1 ≤ p.deterministic := by rw [outer_deterministic_identity]; nlinarith
  rw [upperRate_identity]
  linarith only [hd, hc.2.1, hc.2.2.1, hc.2.2.2]

theorem log_two_mul_bound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.log (2 + a * b) ≤ Real.log (2 + a) + Real.log (2 + b) := by
  have h := Real.log_le_log (by positivity : 0 < 2 + a * b)
    (show 2 + a * b ≤ (2 + a) * (2 + b) by nlinarith)
  rwa [Real.log_mul (by positivity) (by positivity)] at h

theorem outerStepCount_rate (p : Parameters) (hreg : p.ε ^ 2 ≤ p.L * p.gap) :
    (outerStepCount p.L p.gap p.ε : ℝ) ≤ 1000001 * outerGapRatio p := by
  have ha := outerGapRatio_one p hreg
  have h := Nat.ceil_lt_add_one (show 0 ≤ 1000000 * outerGapRatio p by positivity)
  have he : 1000000 * p.L * p.gap / p.ε ^ 2 = 1000000 * outerGapRatio p := by unfold outerGapRatio; ring
  unfold outerStepCount
  rw [he]
  linarith

theorem outer_coarse_noise_identity (p : Parameters) :
    p.σ ^ 2 / (p.μ * outerCoarseTolerance p.L p.ε) = 1000000 * (p.κ * p.σ ^ 2 / p.ε ^ 2) := by
  unfold outerCoarseTolerance Parameters.κ
  field_simp
  ring

theorem outer_fine_noise_identity (p : Parameters) :
    p.σ ^ 2 / (p.μ * outerFineTolerance p.L p.μ p.ε) = 1000000 * p.testing := by
  unfold outerFineTolerance Parameters.testing Parameters.κ
  field_simp
  ring

theorem outer_sqrt_condition (p : Parameters) : Real.sqrt ((3 * p.L) / p.μ) ≤ 2 * Real.sqrt p.κ := by
  have hk : 0 ≤ p.κ := by linarith [p.condition_ge_one]
  calc
    _ ≤ Real.sqrt (4 * p.κ) := Real.sqrt_le_sqrt (by rw [mul_div_assoc]; change 3 * p.κ ≤ 4 * p.κ; linarith)
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num

end FreshGradientMinimax
