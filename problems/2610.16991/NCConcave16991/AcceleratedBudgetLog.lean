import NCConcave16991.AcceleratedBudgetScales

/-! # The actual public SVRG epoch count has only the paper's logarithmic loss -/

noncomputable section

namespace NCConcave16991.Accelerated

def rateBase (p : ProblemParameters) : ℝ :=
  2 + (p.n : ℝ) + dimensionlessA p + dimensionlessB p

def residualArgument (p : ProblemParameters) : ℝ :=
  36 * (4 * p.L) ^ 2 * publicProductDiameter p ^ 2 /
    (publicResidualTolerance p ^ 2 * stageFailure p)

theorem rateBase_bounds (p : ProblemParameters) :
    3 ≤ rateBase p ∧ 1 + dimensionlessA p ≤ rateBase p ∧
      1 + dimensionlessB p ≤ rateBase p ∧ 2 + dimensionlessA p + dimensionlessB p ≤ rateBase p := by
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n_pos
  have hA := (dimensionlessA_pos p).le
  have hB := dimensionlessB_nonneg p
  dsimp [rateBase]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem publicResidualTolerance_eq (p : ProblemParameters) :
    publicResidualTolerance p = p.epsilon ^ 2 /
      (576 * p.L * (dualHorizon p : ℝ) * publicProductDiameter p) := by
  change outerTolerance p / (2 * (dualHorizon p : ℝ) * publicProductDiameter p) = _
  dsimp [outerTolerance]
  ring

theorem residualArgument_eq (p : ProblemParameters) :
    residualArgument p = (1728 * 16 * 288 ^ 2 : ℝ) * (outerHorizon p : ℝ) *
      (dualHorizon p : ℝ) ^ 3 * (p.L * publicProductDiameter p / p.epsilon) ^ 4 := by
  have hS : (outerHorizon p : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (outerHorizon_bounds p).1
  have hK : (dualHorizon p : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (dualHorizon_pos p)
  have hd := (publicProductDiameter_pos p).ne'
  dsimp [residualArgument]
  rw [publicResidualTolerance_eq]
  dsimp [stageFailure]
  field_simp [hS, hK, hd, p.L_pos.ne', p.epsilon_pos.ne']
  <;> ring

theorem residualArgument_bound (p : ProblemParameters) :
    residualArgument p ≤ (2 : ℝ) ^ 100 * rateBase p ^ 8 := by
  let H := rateBase p
  let d := p.L * publicProductDiameter p / p.epsilon
  have hH : 0 ≤ H := le_trans (by norm_num) (rateBase_bounds p).1
  have hd : 0 ≤ d := by
    have hL := p.L_pos; have hD := publicProductDiameter_pos p; have he := p.epsilon_pos
    dsimp [d]; positivity
  have hS : (outerHorizon p : ℝ) ≤ 97 * H :=
    (outerHorizon_bounds p).2.2.trans (mul_le_mul_of_nonneg_left (rateBase_bounds p).2.1 (by norm_num))
  have hK : (dualHorizon p : ℝ) ≤ 36 * H :=
    (dualHorizon_coarse_bound p).trans (mul_le_mul_of_nonneg_left (rateBase_bounds p).2.2.1 (by norm_num))
  have hD : d ≤ 20 * H :=
    (publicProductDiameter_scale_bound p).trans (mul_le_mul_of_nonneg_left (rateBase_bounds p).2.2.2 (by norm_num))
  have hK3 := pow_le_pow_left₀ (Nat.cast_nonneg (dualHorizon p) : (0 : ℝ) ≤ dualHorizon p) hK 3
  have hd4 := pow_le_pow_left₀ hd hD 4
  have hSK := mul_le_mul hS hK3
    (pow_nonneg (Nat.cast_nonneg (dualHorizon p) : (0 : ℝ) ≤ dualHorizon p) 3)
    (show 0 ≤ 97 * H by positivity)
  have hprod := mul_le_mul hSK hd4 (pow_nonneg hd 4)
    (show 0 ≤ (97 * H) * (36 * H) ^ 3 by positivity)
  have hm := mul_le_mul_of_nonneg_left hprod (show (0 : ℝ) ≤ 1728 * 16 * 288 ^ 2 by norm_num)
  have hcoef : (1728 * 16 * 288 ^ 2 : ℝ) * 97 * 36 ^ 3 * 20 ^ 4 ≤ (2 : ℝ) ^ 100 := by norm_num
  have hc := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hH 8)
  rw [residualArgument_eq]
  change (1728 * 16 * 288 ^ 2 : ℝ) * (outerHorizon p : ℝ) * (dualHorizon p : ℝ) ^ 3 * d ^ 4 ≤ _
  apply le_trans ?_ hc
  convert hm using 1 <;> ring

theorem residualArgument_pos (p : ProblemParameters) : 0 < residualArgument p := by
  have hL := p.L_pos
  have hd := publicProductDiameter_pos p
  have hζ := publicResidualTolerance_pos p
  have hf := stageFailure_pos p
  dsimp [residualArgument]
  positivity

theorem publicSolverEpochs_bound (p : ProblemParameters) :
    (publicSolverEpochs p : ℝ) ≤ 109 * complexityLog p := by
  have hH : 0 < rateBase p := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) (rateBase_bounds p).1
  have hlog := Real.log_le_log (residualArgument_pos p) (residualArgument_bound p)
  have heq : Real.log ((2 : ℝ) ^ 100 * rateBase p ^ 8) =
      100 * Real.log 2 + 8 * complexityLog p := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    rfl
  rw [heq] at hlog
  have h2 : Real.log 2 ≤ 1 := by have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); norm_num at hh; exact hh
  have h3 : 1 ≤ Real.log 3 := by
    apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)).2
    exact Real.exp_one_lt_three.le
  have h3p : 0 < Real.log 3 := by linarith
  have hℓ := complexityLog_one_le_public p
  have hquot : Real.log (residualArgument p) / Real.log 3 ≤ 108 * complexityLog p := by
    apply (div_le_iff₀ h3p).2
    have hm := mul_le_mul_of_nonneg_left h3 (show 0 ≤ 108 * complexityLog p by linarith)
    nlinarith only [hlog, h2, hℓ, hm]
  have hJ : (publicSolverEpochs p : ℝ) <
      max 0 (Real.log (residualArgument p) / Real.log 3) + 1 :=
    SVRG.residualEpochCount_bound
  have hm : max 0 (Real.log (residualArgument p) / Real.log 3) ≤ 108 * complexityLog p :=
    max_le (by linarith) hquot
  linarith

end NCConcave16991.Accelerated
