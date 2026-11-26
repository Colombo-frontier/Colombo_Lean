import Bilevel.SmallGapMean

/-! Exact initial hyperderivatives and the source-scale hypergradient budget. -/

noncomputable section
namespace Bilevel.SmallGapInstance.Parameters

open Filter SmallGapProfiles SmallGapProfileBounds SmallGapLiftSupport
open scoped Topology

variable (P : Parameters)

def realizedGradient (ω x : ℝ) : ℝ := Bowl.slope P.L x +
  (P.L / P.μ) * deriv (P.residual ω) (P.L / P.μ * x)

theorem realizedObjective_eq_residual (ω : ℝ) :
    P.realizedObjective ω = fun x => Bowl.value P.L x + P.residual ω (P.L / P.μ * x) := by
  funext x
  rw [realizedObjective, P.upper_response]
  unfold residual
  ring

theorem realizedGradient_correct (ω x : ℝ) :
    HasDerivAt (P.realizedObjective ω) (P.realizedGradient ω x) x := by
  rw [P.realizedObjective_eq_residual]
  have hr := (P.residual_hasDerivAt ω (P.L / P.μ * x)).comp x
    ((hasDerivAt_id x).const_mul (P.L / P.μ))
  convert (Bowl.hasDerivAt_value P.L x).add hr using 1
  unfold realizedGradient
  ring

theorem realizedGradient_hasDerivAt (ω x : ℝ) :
    HasDerivAt (P.realizedGradient ω)
      (P.L / Real.sqrt (1 + x ^ 2) ^ 3 +
        (P.L / P.μ) ^ 2 * deriv (deriv (P.residual ω)) (P.L / P.μ * x)) x := by
  have hr := (deriv_hasDerivAt (P.residual_contDiff ω) (P.L / P.μ * x)).comp x
    ((hasDerivAt_id x).const_mul (P.L / P.μ))
  convert (Bowl.hasDerivAt_slope P.L x).add (hr.const_mul (P.L / P.μ)) using 1
  ring

theorem realizedGradient_derivative_bound (ω x : ℝ) (hω : |ω| ≤ 1) :
    |deriv (P.realizedGradient ω) x| ≤ P.L + 2 * C * (P.L / P.μ) ^ 2 * P.S := by
  have hb := Bowl.curvature_bounds P.L x P.L_pos
  rw [(Bowl.hasDerivAt_slope P.L x).deriv] at hb
  have hr := (P.residual_jet_bounds ω (P.L / P.μ * x) hω).2.2
  have hmul := mul_le_mul_of_nonneg_left hr (sq_nonneg (P.L / P.μ))
  rw [(P.realizedGradient_hasDerivAt ω x).deriv]
  have ht := abs_add (P.L / Real.sqrt (1 + x ^ 2) ^ 3)
    ((P.L / P.μ) ^ 2 * deriv (deriv (P.residual ω)) (P.L / P.μ * x))
  rw [abs_of_pos hb.1, abs_mul, abs_of_nonneg (sq_nonneg (P.L / P.μ))] at ht
  nlinarith

theorem realizedObjective_gradient_lipschitz (ω : ℝ) (hω : |ω| ≤ 1) (x x' : ℝ) :
    |deriv (P.realizedObjective ω) x - deriv (P.realizedObjective ω) x'| ≤
      (P.L + 2 * C * (P.L / P.μ) ^ 2 * P.S) * |x - x'| := by
  have hC := C_pos
  have hL := P.L_pos
  have hS := P.S_pos
  have hlip : LipschitzWith ⟨P.L + 2 * C * (P.L / P.μ) ^ 2 * P.S, by positivity⟩
      (P.realizedGradient ω) := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun t => (P.realizedGradient_hasDerivAt ω t).differentiableAt)
    intro t
    exact P.realizedGradient_derivative_bound ω t hω
  rw [(P.realizedGradient_correct ω x).deriv, (P.realizedGradient_correct ω x').deriv]
  exact hlip.dist_le_mul x x'

/-- Under the source condition `S = L θ ≥ L`, the actual hypergradient is
globally Lipschitz with the claimed numerical multiple of `Γ = κ² S`. -/
theorem realizedObjective_gradient_rate (ω : ℝ) (hω : |ω| ≤ 1) (hS : P.L ≤ P.S) (x x' : ℝ) :
    |deriv (P.realizedObjective ω) x - deriv (P.realizedObjective ω) x'| ≤
      (1 + 2 * C) * ((P.L / P.μ) ^ 2 * P.S) * |x - x'| := by
  have hκ : 1 ≤ P.L / P.μ := (one_le_div P.μ_pos).mpr P.μ_le_L
  have hκ2 : 1 ≤ (P.L / P.μ) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hκ2 P.S_pos.le
  have hc : P.L + 2 * C * (P.L / P.μ) ^ 2 * P.S ≤
      (1 + 2 * C) * ((P.L / P.μ) ^ 2 * P.S) := by nlinarith
  exact (P.realizedObjective_gradient_lipschitz ω hω x x').trans
    (mul_le_mul_of_nonneg_right hc (abs_nonneg _))

theorem realizedObjective_derivative_zero (hgeometry : P.Geometry) (ω : ℝ) :
    deriv (P.realizedObjective ω) 0 = -ω * ((P.L / P.μ) * P.S * P.δ) := by
  rw [(P.realizedObjective_hasDerivAt hgeometry ω 0).deriv]
  have h := (P.separationParameters hgeometry).gradient_core ω 0
    (by simp [separationParameters, P.δ_pos.le])
  rw [h]
  simp [SmallGapSeparation.Parameters.gamma, separationParameters, Bowl.slope]

theorem realizedObjective_second_derivative_zero (hgeometry : P.Geometry) (ω : ℝ) :
    deriv (deriv (P.realizedObjective ω)) 0 = (P.L / P.μ) ^ 2 * P.S + P.L := by
  let Q := P.separationParameters hgeometry
  have he : deriv (P.realizedObjective ω) =ᶠ[𝓝 (0 : ℝ)]
      fun x => Bowl.slope P.L x + Q.curvature * x - ω * Q.gamma := by
    have hδ : |Q.κ * (0 : ℝ)| < 2 * Q.δ := by
      simp only [mul_zero, abs_zero]
      linarith [Q.δ_pos]
    filter_upwards [(continuous_abs.comp (continuous_const.mul continuous_id)).tendsto (0 : ℝ)
      |>.eventually (eventually_lt_nhds hδ)] with x hx
    rw [(P.realizedObjective_hasDerivAt hgeometry ω x).deriv]
    exact Q.gradient_core ω x hx.le
  have hd := ((Bowl.hasDerivAt_slope P.L (0 : ℝ)).add
    ((hasDerivAt_id (0 : ℝ)).const_mul Q.curvature)).sub_const (ω * Q.gamma)
  have h := (hd.congr_of_eventuallyEq he).deriv
  simpa [Q, SmallGapSeparation.Parameters.curvature, separationParameters, add_comm] using h

end Bilevel.SmallGapInstance.Parameters
