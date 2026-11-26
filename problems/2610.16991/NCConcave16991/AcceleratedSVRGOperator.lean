import NCConcave16991.AcceleratedProx
import NCConcave16991.AcceleratedResidual
import NCConcave16991.SVRGParameters

/-! # The actual finite-sum proximal saddle operator, uniformly in the extrapolated dual center -/

noncomputable section

open Set MeasureTheory Metric
open scoped InnerProductSpace BigOperators

namespace NCConcave16991.Accelerated

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}

/-- Actual signed component gradients plus the known common proximal correction. -/
def proximalComponents (P : Problem p dx dy K) (τ : ℝ) (v : DualSpace dy) (c : PrimalSpace dx)
    (i : Fin p.n) (z : JointSpace dx dy) : JointSpace dx dy :=
  signedComponentGradient P i z + saddleCorrection p.L τ v c z

 theorem average_proximalComponents (P : Problem p dx dy K) (τ : ℝ) (v : DualSpace dy)
    (c : PrimalSpace dx) (z : JointSpace dx dy) :
    averageMap (proximalComponents P τ v c) z = saddleOperator P τ v c z := by
  have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.n_pos)
  rw [saddleOperator_eq_signed_plus_correction, ← averageMap_signedComponentGradient]
  simp only [averageMap, proximalComponents, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_add]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn, one_smul]

/-- This is precisely the actual gradient operator of the compact dual proximal saddle. -/
theorem proximalOperator_ballSaddle (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (Δ τ : ℝ) (y0 v : DualSpace dy) (c : PrimalSpace dx) (z : JointSpace dx dy) :
    proximalOperator (ballSaddle P hAS Δ y0 c) τ v z = saddleOperator P τ v c z := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · rfl
  · change -saddleDualGradient P 0 y0 z + τ • (z.snd - v) = -saddleDualGradient P τ v z
    simp only [saddleDualGradient, zero_smul, sub_zero]
    module

 theorem proximalComponents_averagedSmooth (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {τ : ℝ} (hτ : 0 < τ) (hτL : τ ≤ p.L) (Δ : ℝ) (y0 v : DualSpace dy) (c : PrimalSpace dx) :
    AveragedSmooth (proximalComponents P τ v c) (feasibleProduct (ballSaddle P hAS Δ y0 c)) (4 * p.L) := by
  have hG : AveragedSmooth (signedComponentGradient P) (feasibleProduct (ballSaddle P hAS Δ y0 c)) p.L := by
    intro z hz w hw
    exact signedComponentGradient_averagedSmooth P hAS z hz.2 w hw.2
  have hR : ∀ z ∈ feasibleProduct (ballSaddle P hAS Δ y0 c),
      ∀ w ∈ feasibleProduct (ballSaddle P hAS Δ y0 c),
      ‖saddleCorrection p.L τ v c z - saddleCorrection p.L τ v c w‖ ≤ 2 * p.L * ‖z - w‖ := by
    intro z hz w hw
    exact saddleCorrection_lipschitz p.L τ p.L_pos.le hτ.le hτL v c z w
  have hreg := hG.regularize p.n_pos (0 : JointSpace dx dy) p.L_pos.le
    (show 0 ≤ 2 * p.L by linarith [p.L_pos]) hR
  intro z hz w hw
  have hh := hreg z hz w hw
  simp only [add_zero] at hh
  change (p.n : ℝ)⁻¹ * ∑ i, ‖proximalComponents P τ v c i z - proximalComponents P τ v c i w‖ ^ 2 ≤ _ at hh
  have hs : (p.L + 2 * p.L) ^ 2 * ‖z - w‖ ^ 2 ≤ (4 * p.L) ^ 2 * ‖z - w‖ ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg p.L) (sq_nonneg ‖z - w‖)]
  exact hh.trans hs

/-- Strong monotonicity is uniform in v, even when v is outside the known dual domain. -/
theorem proximalComponents_strongMono (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {τ : ℝ} (hτL : τ ≤ p.L) (Δ : ℝ) (y0 v : DualSpace dy) (c : PrimalSpace dx)
    (z : JointSpace dx dy) (hz : z ∈ feasibleProduct (ballSaddle P hAS Δ y0 c))
    (w : JointSpace dx dy) (hw : w ∈ feasibleProduct (ballSaddle P hAS Δ y0 c)) :
    τ * ‖z - w‖ ^ 2 ≤
      ⟪averageMap (proximalComponents P τ v c) z - averageMap (proximalComponents P τ v c) w, z - w⟫_ℝ := by
  rw [average_proximalComponents, average_proximalComponents]
  have hm := saddleOperator_anisotropic_monotone P hAS τ v c z w hz.2 hw.2
  rw [joint_difference_norm_sq]
  nlinarith only [hm, mul_le_mul_of_nonneg_right hτL (sq_nonneg ‖z.fst - w.fst‖)]

/-- A known anchor belongs to every extrapolated proximal subproblem. -/
def proximalAnchor (P : Problem p dx dy K) (hAS : P.averagedSmooth) (Δ : ℝ)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx) :
    feasibleProduct (ballSaddle P hAS Δ y0 c) :=
  ⟨jointPoint c y0, by simpa [feasibleProduct, ballSaddle, compactProximalSaddle, jointPoint] using
    (show c ∈ closedBall c (publicRadius p Δ) ∧ y0 ∈ K.carrier from
      ⟨by simpa using (publicRadius_pos p Δ).le, hy0⟩)⟩

 theorem proximalProduct_diameter (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (Δ : ℝ) (y0 : DualSpace dy) (c : PrimalSpace dx)
    (z : JointSpace dx dy) (hz : z ∈ feasibleProduct (ballSaddle P hAS Δ y0 c))
    (w : JointSpace dx dy) (hw : w ∈ feasibleProduct (ballSaddle P hAS Δ y0 c)) :
    ‖z - w‖ ≤ 2 * publicRadius p Δ + p.diameter := by
  have hx := closedBall_diameter c z.fst hz.1 w.fst hw.1
  have hy := K.diameter_bound z.snd hz.2 w.snd hw.2
  have ht := norm_add_le (jointPoint (z.fst - w.fst) (0 : DualSpace dy))
    (jointPoint (0 : PrimalSpace dx) (z.snd - w.snd))
  have hid : jointPoint (z.fst - w.fst) (0 : DualSpace dy) + jointPoint (0 : PrimalSpace dx) (z.snd - w.snd) = z - w := by
    apply WithLp.ofLp_injective
    apply Prod.ext <;> simp [jointPoint]
  rw [hid] at ht
  change ‖z - w‖ ≤ ‖WithLp.toLp 2 (z.fst - w.fst, (0 : DualSpace dy))‖ +
    ‖WithLp.toLp 2 ((0 : PrimalSpace dx), z.snd - w.snd)‖ at ht
  rw [WithLp.norm_toLp_fst, WithLp.norm_toLp_snd] at ht
  linarith

end NCConcave16991.Accelerated



