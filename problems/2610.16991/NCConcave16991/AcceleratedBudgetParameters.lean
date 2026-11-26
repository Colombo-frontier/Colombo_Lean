import NCConcave16991.AcceleratedStochasticProx
import NCConcave16991.TheoremStatements
import NCConcave16991.SVRGQueries
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Public numerical parameters of the accelerated upper algorithm -/

noncomputable section

namespace NCConcave16991.Accelerated

def outerHorizon (p : ProblemParameters) : ℕ := Nat.ceil (96 * (1 + dimensionlessA p))
def outerTolerance (p : ProblemParameters) : ℝ := p.epsilon ^ 2 / (288 * p.L)
def gapCap (p : ProblemParameters) : ℝ := p.gap + (outerHorizon p : ℝ) * outerTolerance p
def dualRegularization (p : ProblemParameters) : ℝ := p.L / Real.sqrt (p.n : ℝ)
def dualHorizon (p : ProblemParameters) : ℕ := horizon (dualRegularization p) p.diameter (outerTolerance p)
def stageFailure (p : ProblemParameters) : ℝ := 1 / (12 * (outerHorizon p : ℝ) * dualHorizon p)
def publicProductDiameter (p : ProblemParameters) : ℝ := 2 * publicRadius p (gapCap p) + p.diameter
def publicResidualTolerance (p : ProblemParameters) : ℝ :=
  proxTolerance p (gapCap p) (dualRegularization p) (outerTolerance p)
def publicSolverEpochs (p : ProblemParameters) : ℕ :=
  solverEpochCount p (gapCap p) (dualRegularization p) (publicResidualTolerance p) (stageFailure p)
def publicResidualBudget (p : ProblemParameters) : ℕ :=
  SVRG.residualQueryBudget p.n (4 * p.L) (dualRegularization p) (publicSolverEpochs p)
def publicAcceleratedBudget (p : ProblemParameters) : ℕ :=
  outerHorizon p * dualHorizon p * publicResidualBudget p

theorem outerHorizon_bounds (p : ProblemParameters) :
    0 < outerHorizon p ∧ 96 * (1 + dimensionlessA p) ≤ (outerHorizon p : ℝ) ∧
      (outerHorizon p : ℝ) ≤ 97 * (1 + dimensionlessA p) := by
  have hA := dimensionlessA_pos p
  have hp : 0 < 96 * (1 + dimensionlessA p) := by linarith
  refine ⟨Nat.one_le_ceil_iff.mpr hp, Nat.le_ceil _, ?_⟩
  have hh := Nat.ceil_lt_add_one hp.le
  change (Nat.ceil (96 * (1 + dimensionlessA p)) : ℝ) ≤ 97 * (1 + dimensionlessA p)
  linarith

theorem outerTolerance_pos (p : ProblemParameters) : 0 < outerTolerance p := by
  exact div_pos (sq_pos_of_pos p.epsilon_pos) (mul_pos (by norm_num) p.L_pos)

theorem gapCap_pos (p : ProblemParameters) : 0 < gapCap p := by
  have hgap := p.gap_pos
  have hδ := (outerTolerance_pos p).le
  dsimp [gapCap]
  positivity

theorem dualRegularization_pos (p : ProblemParameters) : 0 < dualRegularization p := by
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  exact div_pos p.L_pos (Real.sqrt_pos.mpr hn)

theorem dualRegularization_le_L (p : ProblemParameters) : dualRegularization p ≤ p.L := by
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n_pos
  have hs : 1 ≤ Real.sqrt (p.n : ℝ) := Real.one_le_sqrt.mpr hn
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hs)).mpr
  nlinarith [p.L_pos]

theorem dualHorizon_pos (p : ProblemParameters) : 0 < dualHorizon p := horizon_pos _ _ _

theorem stageFailure_pos (p : ProblemParameters) : 0 < stageFailure p := by
  have hS : (0 : ℝ) < outerHorizon p := by exact_mod_cast (outerHorizon_bounds p).1
  have hK : (0 : ℝ) < dualHorizon p := by exact_mod_cast dualHorizon_pos p
  dsimp [stageFailure]
  positivity

theorem publicProductDiameter_pos (p : ProblemParameters) : 0 < publicProductDiameter p := by
  have hR := publicRadius_pos p (gapCap p)
  have hD := p.diameter_nonneg
  dsimp [publicProductDiameter]
  positivity

theorem publicResidualTolerance_pos (p : ProblemParameters) : 0 < publicResidualTolerance p :=
  proxTolerance_pos p (outerTolerance_pos p)

theorem totalFailure_budget (p : ProblemParameters) :
    (outerHorizon p : ℝ) * ((dualHorizon p : ℝ) * stageFailure p) = 1 / 12 := by
  have hS : (outerHorizon p : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (outerHorizon_bounds p).1
  have hK : (dualHorizon p : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (dualHorizon_pos p)
  dsimp [stageFailure]
  field_simp [hS, hK]

theorem complexityLog_one_le_public (p : ProblemParameters) : 1 ≤ complexityLog p := by
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n_pos
  have hA := (dimensionlessA_pos p).le
  have hB := dimensionlessB_nonneg p
  have hq : 3 ≤ 2 + (p.n : ℝ) + dimensionlessA p + dimensionlessB p := by linarith
  unfold complexityLog
  apply (Real.le_log_iff_exp_le (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) hq)).2
  linarith [Real.exp_one_lt_three]

end NCConcave16991.Accelerated
