import NCConcave16991.AcceleratedCenterGradient
import Mathlib.Topology.Sequences

/-! # Actual proximal saddles as dual regularization vanishes -/

noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace NCConcave16991

def vanishingRegularization (p : ProblemParameters) (j : ℕ) : ℝ := p.L / ((j : ℝ) + 1)

theorem vanishingRegularization_pos (p : ProblemParameters) (j : ℕ) :
    0 < vanishingRegularization p j := div_pos p.L_pos (by positivity)

theorem vanishingRegularization_le_L (p : ProblemParameters) (j : ℕ) :
    vanishingRegularization p j ≤ p.L := by
  apply (div_le_iff₀ (by positivity : 0 < (j : ℝ) + 1)).2
  nlinarith [mul_nonneg p.L_pos.le (Nat.cast_nonneg j)]

theorem vanishingRegularization_tendsto (p : ProblemParameters) :
    Tendsto (vanishingRegularization p) atTop (𝓝 0) := by
  change Tendsto (fun j : ℕ ↦ p.L / ((j : ℝ) + 1)) atTop (𝓝 0)
  simpa only [div_eq_mul_inv, one_mul, mul_zero] using
    (tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun j : ℕ ↦ p.L * (1 / ((j : ℝ) + 1))) atTop (𝓝 (p.L * 0)))

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}

def vanishingSaddle (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (c : PrimalSpace dx) (j : ℕ) : JointSpace dx dy :=
  tiltedSaddleSolution P hAS (vanishingRegularization_pos p j)
    (vanishingRegularization_le_L p j) y0 c 0

theorem vanishingSaddle_spec (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (c : PrimalSpace dx) (j : ℕ) :
    VariationalInequality.IsSolution (productDomain dx K)
      (tiltedSaddleOperator P (vanishingRegularization p j) y0 c 0)
      (vanishingSaddle P hAS y0 c j) :=
  tiltedSaddleSolution_spec P hAS (vanishingRegularization_pos p j)
    (vanishingRegularization_le_L p j) y0 c 0

theorem vanishingSaddle_primal_error (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx) (j : ℕ) :
    4 * p.L ^ 2 * ‖(vanishingSaddle P hAS y0 c j).fst -
      proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c‖ ^ 2 ≤
        2 * p.L * vanishingRegularization p j * p.diameter ^ 2 := by
  have hh := dualRegularization_moreau_gradient_error P hAS
    (vanishingRegularization_pos p j).le y0 hy0 c
  rw [(P.moreau_hasGradientAt hAS c).gradient,
    (dualRegularizedEnvelope_hasGradientAt P hAS (vanishingRegularization_pos p j).le y0 hy0 c).gradient,
    ← tiltedSaddleSolution_unbiased_primal_eq_proximalMap P hAS
      (vanishingRegularization_pos p j) (vanishingRegularization_le_L p j) y0 hy0 c] at hh
  have he : (2 * p.L) • (c - proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c) -
      (2 * p.L) • (c - (vanishingSaddle P hAS y0 c j).fst) =
      (2 * p.L) • ((vanishingSaddle P hAS y0 c j).fst -
        proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c) := by module
  change ‖(2 * p.L) • (c - proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c) -
      (2 * p.L) • (c - (vanishingSaddle P hAS y0 c j).fst)‖ ^ 2 ≤ _ at hh
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (show 0 < 2 * p.L by linarith [p.L_pos]), mul_pow] at hh
  convert hh using 1 <;> ring

theorem vanishingSaddle_primal_tendsto (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx) :
    Tendsto (fun j ↦ (vanishingSaddle P hAS y0 c j).fst) atTop
      (𝓝 (proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hlim : Tendsto (fun j ↦ 2 * p.L * vanishingRegularization p j * p.diameter ^ 2)
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      ((vanishingRegularization_tendsto p).const_mul (2 * p.L)).mul_const (p.diameter ^ 2)
  have hp : 0 < 4 * p.L ^ 2 * ε ^ 2 := mul_pos
    (mul_pos (by norm_num) (sq_pos_of_pos p.L_pos)) (sq_pos_of_pos hε)
  have he := (tendsto_order.1 hlim).2 _ hp
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  refine ⟨N, ?_⟩
  intro j hj
  have hb := vanishingSaddle_primal_error P hAS y0 hy0 c j
  have hs : ‖(vanishingSaddle P hAS y0 c j).fst -
      proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c‖ ^ 2 < ε ^ 2 := by
    nlinarith only [hb, hN j hj, sq_pos_of_pos p.L_pos]
  rw [dist_eq_norm]
  nlinarith [norm_nonneg ((vanishingSaddle P hAS y0 c j).fst -
    proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c)]

end NCConcave16991
