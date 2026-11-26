import NCConcave16991.InnerSaddle

/-! # Bias transfer and the complete source inner-error bound -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators InnerProductSpace

namespace NCConcave16991

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}
  [MeasurableSpace (Fin p.n)] [MeasurableSingletonClass (Fin p.n)]

local instance : NeZero p.n := ⟨Nat.ne_of_gt p.n_pos⟩

/-- The actual anisotropic squared anchor-bias penalty. -/
def innerBiasEnergy (p : ProblemParameters) (μ : ℝ) (ξ : JointSpace dx dy) : ℝ :=
  ‖ξ.fst‖ ^ 2 / p.L ^ 2 + ‖ξ.snd‖ ^ 2 / (p.L * μ)

 theorem innerBiasEnergy_nonneg {μ : ℝ} (hμ : 0 < μ) (ξ : JointSpace dx dy) :
    0 ≤ innerBiasEnergy p μ ξ := by
  dsimp [innerBiasEnergy]
  exact add_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))
    (div_nonneg (sq_nonneg _) (mul_pos p.L_pos hμ).le)

/-- The actual average is compared to the unbiased saddle, with the sharp bias energy. -/
theorem independentInner_bias_transfer (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ p.L) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier)
    (c : PrimalSpace dx) (ξ : JointSpace dx dy) {k : ℕ}
    (hk : 4294967296 * (p.L / μ) ^ 2 ≤ (k : ℝ)) :
    independentInnerMeanError P μ y0 hy0 c ξ
      (tiltedSaddleSolution P hAS hμ hμL y0 c 0).fst k ≤
        (1 / 1024 : ℝ) * ‖(tiltedSaddleSolution P hAS hμ hμL y0 c 0).fst - c‖ ^ 2 +
          3 * innerBiasEnergy p μ ξ + 6 / (65536 * (p.L / μ)) * p.diameter ^ 2 := by
  let p0 := (tiltedSaddleSolution P hAS hμ hμL y0 c 0).fst
  let pξ := (tiltedSaddleSolution P hAS hμ hμL y0 c ξ).fst
  let B := innerBiasEnergy p μ ξ
  let A := 3 / (65536 * (p.L / μ))
  have hκpos : 0 < p.L / μ := div_pos p.L_pos hμ
  have hκ : 1 ≤ p.L / μ := by apply (le_div_iff₀ hμ).mpr; simpa using hμL
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hA : A ≤ 3 / 65536 := by
    dsimp [A]
    apply (div_le_iff₀ (by positivity : 0 < 65536 * (p.L / μ))).mpr
    nlinarith
  have hB : 0 ≤ B := innerBiasEnergy_nonneg hμ ξ
  have hs : ‖pξ - p0‖ ^ 2 ≤ B := tiltedSaddleSolution_primal_sensitivity P hAS hμ hμL y0 c ξ
  have hc : ‖pξ - c‖ ^ 2 ≤ 2 * ‖p0 - c‖ ^ 2 + 2 * B := by
    have h := InnerAlgorithm.anchor_distance_sq pξ p0 c
    nlinarith
  have hf := independentInner_first_bound P hAS hμ hμL y0 hy0 c ξ hk
  have hp (ω : InnerAlgorithm.Seed p.n k) :=
    InnerAlgorithm.anchor_distance_sq (independentInnerOutput P μ y0 hy0 c ξ k ω) pξ p0
  have hi := integral_mono (μ := InnerAlgorithm.seedLaw k) Integrable.of_finite Integrable.of_finite hp
  rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul] at hi
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  change independentInnerMeanError P μ y0 hy0 c ξ p0 k ≤
    2 * independentInnerMeanError P μ y0 hy0 c ξ pξ k + 2 * ‖pξ - p0‖ ^ 2 at hi
  have hcentre := mul_le_mul_of_nonneg_left hc hA0
  have hAx := mul_le_mul_of_nonneg_right hA (sq_nonneg ‖p0 - c‖)
  have hAB := mul_le_mul_of_nonneg_right hA hB
  have hdiam : 6 / (65536 * (p.L / μ)) * p.diameter ^ 2 = 2 * A * p.diameter ^ 2 := by dsimp [A]; ring
  change independentInnerMeanError P μ y0 hy0 c ξ p0 k ≤
    (1 / 1024 : ℝ) * ‖p0 - c‖ ^ 2 + 3 * B + _
  rw [hdiam]
  change independentInnerMeanError P μ y0 hy0 c ξ pξ k ≤ A * (‖pξ - c‖ ^ 2 + p.diameter ^ 2) at hf
  nlinarith

/-- The selected source regularization makes the remaining diameter term sufficiently small. -/
theorem selected_inner_diameter_term (p : ProblemParameters) :
    6 / (65536 * (p.L / selectedDualRegularization p)) * p.diameter ^ 2 ≤
      p.epsilon ^ 2 / (4294967296 * p.L ^ 2) := by
  have hL := p.L_pos
  have hμ := selectedDualRegularization_pos p
  have he := selectedDualRegularization_value_error p
  have hid : 6 / (65536 * (p.L / selectedDualRegularization p)) * p.diameter ^ 2 =
      (12 / (65536 * p.L)) * (selectedDualRegularization p * p.diameter ^ 2 / 2) := by
    field_simp [hL.ne', hμ.ne'] <;> ring
  rw [hid]
  have hm := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 12 / (65536 * p.L))
  have hc : (12 / (65536 * p.L)) * (p.epsilon ^ 2 / (2 ^ 21 * p.L)) ≤
      p.epsilon ^ 2 / (4294967296 * p.L ^ 2) := by
    field_simp [hL.ne']
    nlinarith [sq_nonneg p.epsilon]
  exact hm.trans hc

/-- The complete source inner-error line, for the actual proximal map of the actual regularized value. -/
theorem independentInner_selected_error (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx) (ξ : JointSpace dx dy)
    {k : ℕ} (hk : 4294967296 * (p.L / selectedDualRegularization p) ^ 2 ≤ (k : ℝ)) :
    independentInnerMeanError P (selectedDualRegularization p) y0 hy0 c ξ
      (proximalMap p.L_pos (dualRegularizedValue_continuous P hAS (selectedDualRegularization p) y0)
        (dualRegularizedValue_bddBelow P (selectedDualRegularization_pos p).le y0 hy0) c) k ≤
      (1 / 1024 : ℝ) *
        ‖proximalMap p.L_pos (dualRegularizedValue_continuous P hAS (selectedDualRegularization p) y0)
          (dualRegularizedValue_bddBelow P (selectedDualRegularization_pos p).le y0 hy0) c - c‖ ^ 2 +
        3 * innerBiasEnergy p (selectedDualRegularization p) ξ +
          p.epsilon ^ 2 / (4294967296 * p.L ^ 2) := by
  have h := independentInner_bias_transfer P hAS (selectedDualRegularization_pos p)
    (selectedDualRegularization_le_L p) y0 hy0 c ξ hk
  rw [tiltedSaddleSolution_unbiased_primal_eq_proximalMap P hAS (selectedDualRegularization_pos p)
    (selectedDualRegularization_le_L p) y0 hy0 c] at h
  have hd := selected_inner_diameter_term p
  linarith

end NCConcave16991

