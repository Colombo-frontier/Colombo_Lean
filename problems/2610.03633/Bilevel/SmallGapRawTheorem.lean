import Bilevel.SmallGapJointHessian
import Bilevel.SmallGapStoppedAE

/-! The complete raw fixed-dimensional family, with the exact source parameter
choices. The certificates below bundle proved properties of the actual defined
objectives and oracle; no analytic certificate is an input hypothesis. -/

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace

namespace Bilevel.SmallGapScaling.Input

open SmallGapInstance SmallGapLiftSupport SmallGapProfileBounds

variable (Q : SmallGapScaling.Input)

theorem rawRho_scale : Q.parameters.rawRho = 18640 * C ^ 2 * (Q.L / Q.κ) * Q.θ := by
  dsimp [Parameters.rawRho, parameters]
  field_simp [Q.L_pos.ne']

theorem raw_signal_scale : Q.parameters.signalBound =
    (614 * C ^ 2) * (8 * Q.ε) ^ 2 / (Q.L * Q.θ * Q.κ ^ 3) := by
  rw [Q.signal_scale]
  ring

theorem signal_hasGradientX (x : ℝ) (y : LowerSpace) :
    HasGradientAt (fun _ : ℝ => Q.parameters.signal y) 0 x := by
  exact (hasDerivAt_const x (Q.parameters.signal y)).hasGradientAt'

theorem signal_full_envelope (y : LowerSpace) :
    Real.sqrt (‖(0 : ℝ)‖ ^ 2 + ‖Q.parameters.signalY y‖ ^ 2) ≤
      (614 * C ^ 2) * (8 * Q.ε) ^ 2 / (Q.L * Q.θ * Q.κ ^ 3) := by
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add, Real.sqrt_sq (norm_nonneg _)]
  rw [← Q.raw_signal_scale]
  exact Q.parameters.signal_gradient_bound_of_scale y Q.scale_condition

/-- The two-sign average used in testing is the expectation under an actual
uniform sign distribution, chosen independently before seed and draw laws. -/
theorem uniform_sign_risk (plus minus : ℝ) :
    (∫ b, (if b then plus else minus) ∂BernoulliOracle.law (1 / 2) (by norm_num)) =
      (plus + minus) / 2 := by
  rw [BernoulliOracle.integral_law (1 / 2) (by norm_num) (by norm_num)]
  simp only [Bool.false_eq_true, ↓reduceIte, smul_eq_mul]
  ring

structure RawMeanClaims (ω : ℝ) : Prop where
  lower_hessian : ∀ y v, (Q.L / Q.κ) / 2 * ‖v‖ ^ 2 ≤ ⟪Q.parameters.lowerYY ω y v, v⟫
  lower_smooth : ∀ x x' y y',
    ‖Q.parameters.lowerX ω x y - Q.parameters.lowerX ω x' y'‖ ^ 2 +
      ‖Q.parameters.lowerY ω x y - Q.parameters.lowerY ω x' y'‖ ^ 2 ≤
        (3 * Q.L) ^ 2 * (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2)
  full_hessian_variation : ∀ z z' : Parameters.JointSpace,
    ‖fderiv ℝ (fderiv ℝ (fun v : Parameters.JointSpace => Q.parameters.lower ω v.1 v.2)) z -
      fderiv ℝ (fderiv ℝ (fun v : Parameters.JointSpace => Q.parameters.lower ω v.1 v.2)) z'‖ ≤
        (18640 * C ^ 2 * (Q.L / Q.κ) * Q.θ) * Model.jointDistance z.1 z'.1 z.2 z'.2
  upper_full_bound : ∀ x y,
    Real.sqrt (‖Q.parameters.upperX x y‖ ^ 2 + ‖Q.parameters.upperY x y‖ ^ 2) ≤ Real.sqrt 2 * Q.L
  upper_smooth : ∀ x x' y y',
    ‖Q.parameters.upperX x y - Q.parameters.upperX x' y'‖ ^ 2 +
      ‖Q.parameters.upperY x y - Q.parameters.upperY x' y'‖ ^ 2 ≤
        Q.L ^ 2 * (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2)
  initial_solution : Q.parameters.response ω 0 = 0
  exact_minimizer : ∀ x,
    (∀ y, Q.parameters.lower ω x (Q.parameters.response ω x) ≤ Q.parameters.lower ω x y) ∧
    (∀ y, Q.parameters.lower ω x y ≤ Q.parameters.lower ω x (Q.parameters.response ω x) →
      y = Q.parameters.response ω x)
  response_formula : ∀ x, Q.parameters.response ω x =
    pack (Q.κ * x) (Q.parameters.residual ω (Q.κ * x) / Q.L) 0
  objective_formula : ∀ x, Q.parameters.realizedObjective ω x =
    Bowl.value Q.L x + r0 Q.parameters.S Q.parameters.R (Q.κ * x) -
      ω * r1 Q.parameters.S Q.parameters.δ (Q.κ * x)
  coercive : Filter.Tendsto (Q.parameters.realizedObjective ω) (Filter.cocompact ℝ) Filter.atTop
  hypergradient_lipschitz : ∀ x x',
    |deriv (Q.parameters.realizedObjective ω) x - deriv (Q.parameters.realizedObjective ω) x'| ≤
      (1 + 2 * C) * (Q.κ ^ 2 * (Q.L * Q.θ)) * |x - x'|
  derivative_zero : deriv (Q.parameters.realizedObjective ω) 0 = -ω * (8 * Q.ε)
  second_derivative_zero : deriv (deriv (Q.parameters.realizedObjective ω)) 0 =
    Q.κ ^ 2 * (Q.L * Q.θ) + Q.L
  finite_gap : ∃ xstar, (∀ x, Q.parameters.realizedObjective ω xstar ≤ Q.parameters.realizedObjective ω x) ∧
    (8 * Q.ε) ^ 2 / (2 * (Q.κ ^ 2 * (Q.L * Q.θ) + Q.L)) ≤
      Q.parameters.realizedObjective ω 0 - Q.parameters.realizedObjective ω xstar ∧
    Q.parameters.realizedObjective ω 0 - Q.parameters.realizedObjective ω xstar ≤
      (8 * Q.ε) ^ 2 / (2 * (Q.κ ^ 2 * (Q.L * Q.θ)))

theorem raw_mean_claims (ω : ℝ) (hsign : ω = 1 ∨ ω = -1) : Q.RawMeanClaims ω := by
  have hω : |ω| ≤ 1 := by rcases hsign with h | h <;> simp [h]
  have hs := Q.parameters.smallness_of_scale Q.scale_condition
  constructor
  · intro y v
    exact Q.parameters.hessian_coercive ω y v hω hs.2
  · exact Q.parameters.lower_smooth ω hω hs.2
  · intro z z'
    simpa only [Q.rawRho_scale] using Q.parameters.full_joint_hessian_variation ω hω Q.scale_condition z z'
  · intro x y
    have hb := Q.parameters.upper_gradient_bound x y
    have hL := Q.L_pos
    have hn : 0 ≤ ‖Q.parameters.upperX x y‖ ^ 2 + ‖Q.parameters.upperY x y‖ ^ 2 := by positivity
    have hr := Real.sq_sqrt hn
    have htwo : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hnonneg : 0 ≤ Real.sqrt 2 * Q.L := mul_nonneg (Real.sqrt_nonneg _) hL.le
    change ‖Q.parameters.upperX x y‖ ^ 2 + ‖Q.parameters.upperY x y‖ ^ 2 ≤ 2 * Q.L ^ 2 at hb
    nlinarith [Real.sqrt_nonneg (‖Q.parameters.upperX x y‖ ^ 2 + ‖Q.parameters.upperY x y‖ ^ 2)]
  · exact Q.parameters.upper_smooth
  · exact Q.parameters.response_zero ω
  · intro x
    exact Q.parameters.exact_response ω x hω Q.scale_condition
  · intro x
    unfold Parameters.response
    rw [Q.condition_number]
    rfl
  · intro x
    rw [Parameters.realizedObjective, Q.parameters.upper_response, Q.condition_number]
    rfl
  · exact Q.parameters.realizedObjective_coercive Q.geometry ω
  · intro x x'
    simpa only [Q.Gamma] using Q.parameters.realizedObjective_gradient_rate ω hω Q.S_ge_L x x'
  · simpa only [Q.gamma] using Q.parameters.realizedObjective_derivative_zero Q.geometry ω
  · simpa only [Q.Gamma] using Q.parameters.realizedObjective_second_derivative_zero Q.geometry ω
  · obtain ⟨xstar, hmin⟩ := Q.parameters.realizedObjective_minimum_exists Q.geometry ω
    refine ⟨xstar, hmin, ?_⟩
    simpa only [Q.gamma, Q.Gamma] using Q.parameters.realizedObjective_gap Q.geometry ω xstar hsign hmin

structure RawOracleClaims (σ ω : ℝ) : Prop where
  probability_pos : 0 < Q.parameters.activationProbability σ
  probability_le_one : Q.parameters.activationProbability σ ≤ 1
  sample_C3 : ∀ b, ContDiff ℝ 3 (fun v : ℝ × LowerSpace =>
    Q.parameters.sampleLower (Q.parameters.activationProbability σ) ω v.1 v.2 b)
  sample_gradient_x : ∀ x y b,
    HasGradientAt (fun v => Q.parameters.sampleLower (Q.parameters.activationProbability σ) ω v y b)
      (Q.parameters.sampleLowerX (Q.parameters.activationProbability σ) ω x y b) x
  sample_gradient_y : ∀ x y b,
    HasGradientAt (fun v => Q.parameters.sampleLower (Q.parameters.activationProbability σ) ω x v b)
      (Q.parameters.sampleLowerY (Q.parameters.activationProbability σ) ω x y b) y
  exact_x : ∀ x y b, Q.parameters.sampleLowerX (Q.parameters.activationProbability σ) ω x y b =
    Q.parameters.lowerX ω x y
  mean_y : ∀ x y,
    (∫ b, Q.parameters.sampleLowerY (Q.parameters.activationProbability σ) ω x y b
      ∂BernoulliOracle.law (Q.parameters.activationProbability σ) (Q.parameters.activationProbability_le_one σ)) =
        Q.parameters.lowerY ω x y
  full_variance : ∀ x y,
    (∫ b, (‖Q.parameters.sampleLowerX (Q.parameters.activationProbability σ) ω x y b - Q.parameters.lowerX ω x y‖ ^ 2 +
      ‖Q.parameters.sampleLowerY (Q.parameters.activationProbability σ) ω x y b - Q.parameters.lowerY ω x y‖ ^ 2)
      ∂BernoulliOracle.law (Q.parameters.activationProbability σ) (Q.parameters.activationProbability_le_one σ)) ≤ σ ^ 2
  signal_envelope : ∀ y, ‖Q.parameters.signalY y‖ ≤
    (614 * C ^ 2) * (8 * Q.ε) ^ 2 / (Q.L * Q.θ * Q.κ ^ 3)

theorem raw_oracle_claims (σ ω : ℝ) (hsign : ω = 1 ∨ ω = -1) : Q.RawOracleClaims σ ω where
  probability_pos := Q.parameters.activationProbability_pos σ
  probability_le_one := Q.parameters.activationProbability_le_one σ
  sample_C3 := Q.parameters.sampleLower_joint_contDiff _ ω
  sample_gradient_x := Q.parameters.sampleLower_hasGradientX _ ω
  sample_gradient_y := Q.parameters.sampleLower_hasGradientY _ ω
  exact_x := fun _ _ _ => rfl
  mean_y := fun x y => Q.parameters.sampleLowerY_mean _ ω x y
    (Q.parameters.activationProbability_pos σ) (Q.parameters.activationProbability_le_one σ) hsign
  full_variance := fun x y => Q.parameters.sampleLower_full_variance σ ω x y hsign Q.scale_condition
  signal_envelope := fun y => by
    rw [← Q.raw_signal_scale]
    exact Q.parameters.signal_gradient_bound_of_scale y Q.scale_condition

/-- All clauses of the raw mean and conservative oracle construction hold
simultaneously for the two actual signs, with global stationary separation. -/
theorem raw_family (σ : ℝ) :
    (∀ ω, ω = 1 ∨ ω = -1 → Q.RawMeanClaims ω ∧ Q.RawOracleClaims σ ω) ∧
    (∀ x, 16 * Q.ε ≤ |deriv (Q.parameters.realizedObjective 1) x| +
      |deriv (Q.parameters.realizedObjective (-1)) x|) := by
  constructor
  · intro ω hω
    exact ⟨Q.raw_mean_claims ω hω, Q.raw_oracle_claims σ ω hω⟩
  · intro x
    have h := Q.parameters.realizedObjective_separation Q.geometry x
    rw [Q.gamma] at h
    linarith

end Bilevel.SmallGapScaling.Input
