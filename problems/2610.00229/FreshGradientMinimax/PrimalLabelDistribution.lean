import FreshGradientMinimax.PrimalLabelSuccess

/-! A fixed finite hard distribution defeats every measurable randomized
algorithm under the original coin horizon. This is the coordinate-label version
of C.5; it does not assert the paper's Haar law or its smaller ambient dimension. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory
open scoped BigOperators
namespace Algorithm
variable {n D : ℕ} {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm D D Seed)

theorem primalLabelCoinOutput_measurable (hD : (n + 1) + (n + n) ≤ D)
    (z : Fin ((n + 1) + (n + n)) → Fin D) {L ε μ : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) (hm : μ ≤ L / (4 * primalScalingConstant))
    (σ : ℝ) (N : ℕ) : Measurable (A.primalLabelCoinOutput hD z hL hε hμ hm σ N) :=
  (A.output_measurable N).comp (A.coinRun_measurable _
    (primalCoinReply_measurable (primalLabelFrame hD z) (dualLabelFrame hD z) hL hε hμ hm σ) N)

theorem primalLabelSuccessIndicator_integrable (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hD : (n + 1) + (n + n) ≤ D) (z : Fin ((n + 1) + (n + n)) → Fin D) {L ε μ : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) (hm : μ ≤ L / (4 * primalScalingConstant))
    (σ : ℝ) (N : ℕ) : Integrable (A.primalLabelSuccessIndicator hD z hL hε hμ hm σ N)
      (ν.prod (coinWordLaw (primalRevealProbability L ε μ σ) N)) := by
  letI := coinWordLaw_probability (primalRevealProbability_pos hL hε hμ σ).le
    (primalRevealProbability_le_one L ε μ σ) N
  exact truthValue_integrable _ ((A.primalLabelCoinOutput_measurable hD z hL hε hμ hm σ N)
    ((paperCompressedModel (primalLabelFrame hD z) (dualLabelFrame hD z) hL hε hμ hm).successSet_measurable ε))

theorem primalLabelSuccessIndicator_integral (ν : Measure Seed)
    (hD : (n + 1) + (n + n) ≤ D) (z : Fin ((n + 1) + (n + n)) → Fin D) {L ε μ : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) (hm : μ ≤ L / (4 * primalScalingConstant))
    (σ : ℝ) (N : ℕ) :
    (∫ sw, A.primalLabelSuccessIndicator hD z hL hε hμ hm σ N sw
      ∂ν.prod (coinWordLaw (primalRevealProbability L ε μ σ) N)) =
      (A.outputLaw ν (primalFreshOracle (primalLabelFrame hD z) (dualLabelFrame hD z) hL hε hμ hm σ).kernel N).real
        ((paperCompressedModel (primalLabelFrame hD z) (dualLabelFrame hD z) hL hε hμ hm).successSet ε) := by
  rw [primalFreshOracle_outputLaw (primalLabelFrame hD z) (dualLabelFrame hD z) A ν hL hε hμ hm σ N]
  change _ = ((ν.prod (coinWordLaw (primalRevealProbability L ε μ σ) N)).map
    (A.primalLabelCoinOutput hD z hL hε hμ hm σ N)).real _
  rw [Measure.real, Measure.map_apply (A.primalLabelCoinOutput_measurable hD z hL hε hμ hm σ N)
    ((paperCompressedModel (primalLabelFrame hD z) (dualLabelFrame hD z) hL hε hμ hm).successSet_measurable ε)]
  exact integral_truthValue _ ((A.primalLabelCoinOutput_measurable hD z hL hε hμ hm σ N)
    ((paperCompressedModel (primalLabelFrame hD z) (dualLabelFrame hD z) hL hε hμ hm).successSet_measurable ε))

end Algorithm

theorem primal_finite_label_success_bound (n N : ℕ) (hn : 0 < n) {L ε μ : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) (hm : μ ≤ L / (4 * primalScalingConstant))
    (σ : ℝ) (hN : (N : ℝ) ≤ (n : ℝ) / (12 * primalRevealProbability L ε μ σ))
    {Seed : Type*} [MeasurableSpace Seed]
    (A : Algorithm (primalLabelDimension n N L ε μ) (primalLabelDimension n N L ε μ) Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (𝔼 z : Fin ((n + 1) + (n + n)) → Fin (primalLabelDimension n N L ε μ),
      (A.outputLaw ν (primalFreshOracle (primalLabelFrame (primalLabelDimension_size n N L ε μ) z)
        (dualLabelFrame (primalLabelDimension_size n N L ε μ) z) hL hε hμ hm σ).kernel N).real
        ((paperCompressedModel (primalLabelFrame (primalLabelDimension_size n N L ε μ) z)
          (dualLabelFrame (primalLabelDimension_size n N L ε μ) z) hL hε hμ hm).successSet ε)) ≤ (1 / 6 : ℝ) := by
  letI := coinWordLaw_probability (primalRevealProbability_pos hL hε hμ σ).le
    (primalRevealProbability_le_one L ε μ σ) N
  have hi := fun z => A.primalLabelSuccessIndicator_integrable ν
    (primalLabelDimension_size n N L ε μ) z hL hε hμ hm σ N
  have hc : Integrable (fun sw : Seed × (Fin N → Bool) => truthValue (n ≤ coinSuccessCount sw.2))
      (ν.prod (coinWordLaw (primalRevealProbability L ε μ σ) N)) :=
    integrable_on_product_snd (ν := ν) (ξ := coinWordLaw (primalRevealProbability L ε μ σ) N)
      (g := fun w : Fin N → Bool => truthValue (n ≤ coinSuccessCount w)) Integrable.of_finite
  have h := integral_mono (integrable_finite_average _ hi) (hc.add (integrable_const (1 / 12 : ℝ)))
    (A.primalLabelSuccess_average n N hL hε hμ hm σ)
  simp only [Pi.add_apply] at h
  rw [integral_finite_average _ hi, integral_add hc (integrable_const (1 / 12 : ℝ)),
    integral_fun_snd (fun w : Fin N → Bool => truthValue (n ≤ coinSuccessCount w))] at h
  simp only [A.primalLabelSuccessIndicator_integral, measureReal_univ_eq_one, one_smul,
    integral_const, smul_eq_mul, one_mul] at h
  have he : (∫ w : Fin N → Bool, truthValue (n ≤ coinSuccessCount w)
      ∂coinWordLaw (primalRevealProbability L ε μ σ) N) =
      (coinWordLaw (primalRevealProbability L ε μ σ) N).real {w | n ≤ coinSuccessCount w} :=
    integral_truthValue _ (Set.to_countable _).measurableSet
  rw [he] at h
  have hb := coinSuccessCount_exhaustion (primalRevealProbability_pos hL hε hμ σ)
    (primalRevealProbability_le_one L ε μ σ) hn hN
  linarith

end FreshGradientMinimax
