import FreshGradientMinimax.AcceleratedLabelSuccess

/-! A finite hard distribution chosen before the policy defeats every
measurable randomized algorithm within the accelerated hiding horizon. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory
open scoped BigOperators
namespace Algorithm
variable {n k D : ℕ} {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm D D Seed)

theorem acceleratedLabelActualOutput_measurable (hD : (k * 2 + 1) + k * (n + 2) ≤ D)
    (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D)
    (hn : 10 ≤ n + 2) (hk : 0 < k) {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hchain : (n + 2 : ℝ) ^ 2 ≤ L / (4 * acceleratedSmoothnessConstant * μ)) (H : ℕ) :
    Measurable (A.acceleratedLabelActualOutput hD z hn hk hL hε hμ hchain H) :=
  (A.output_measurable H).comp (A.deterministicRun_measurable _
    (fun _ => (acceleratedPhysicalModel (acceleratedPrimalLabelFrame hD z) (acceleratedDualLabelFrame hD z)
      hn hk hL hε hμ hchain).jointGradient_continuous.measurable) H)

theorem acceleratedLabelSuccessIndicator_integrable (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hD : (k * 2 + 1) + k * (n + 2) ≤ D)
    (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D)
    (hn : 10 ≤ n + 2) (hk : 0 < k) {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hchain : (n + 2 : ℝ) ^ 2 ≤ L / (4 * acceleratedSmoothnessConstant * μ)) (H : ℕ) :
    Integrable (A.acceleratedLabelSuccessIndicator hD z hn hk hL hε hμ hchain H) ν :=
  truthValue_integrable ν ((A.acceleratedLabelActualOutput_measurable hD z hn hk hL hε hμ hchain H)
    ((acceleratedPhysicalModel (acceleratedPrimalLabelFrame hD z) (acceleratedDualLabelFrame hD z)
      hn hk hL hε hμ hchain).successSet_measurable ε))

theorem acceleratedLabelSuccessIndicator_integral (ν : Measure Seed)
    (hD : (k * 2 + 1) + k * (n + 2) ≤ D)
    (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D)
    (hn : 10 ≤ n + 2) (hk : 0 < k) {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hchain : (n + 2 : ℝ) ^ 2 ≤ L / (4 * acceleratedSmoothnessConstant * μ)) (σ : ℝ) (H : ℕ) :
    (∫ seed, A.acceleratedLabelSuccessIndicator hD z hn hk hL hε hμ hchain H seed ∂ν) =
      (A.outputLaw ν (FreshOracle.exact
        (acceleratedPhysicalModel (acceleratedPrimalLabelFrame hD z) (acceleratedDualLabelFrame hD z)
          hn hk hL hε hμ hchain) σ).kernel H).real
        ((acceleratedPhysicalModel (acceleratedPrimalLabelFrame hD z) (acceleratedDualLabelFrame hD z)
          hn hk hL hε hμ hchain).successSet ε) := by
  let F := acceleratedPhysicalModel (acceleratedPrimalLabelFrame hD z) (acceleratedDualLabelFrame hD z)
    hn hk hL hε hμ hchain
  change (∫ seed, A.acceleratedLabelSuccessIndicator hD z hn hk hL hε hμ hchain H seed ∂ν) =
    (A.outputLaw ν (ProbabilityTheory.Kernel.deterministic F.jointGradient
      F.jointGradient_continuous.measurable) H).real (F.successSet ε)
  rw [A.outputLaw_exact ν F.jointGradient_continuous.measurable H]
  change (∫ seed, A.acceleratedLabelSuccessIndicator hD z hn hk hL hε hμ hchain H seed ∂ν) =
    (ν.map (A.acceleratedLabelActualOutput hD z hn hk hL hε hμ hchain H)).real (F.successSet ε)
  rw [Measure.real, Measure.map_apply (A.acceleratedLabelActualOutput_measurable hD z hn hk hL hε hμ hchain H)
    (F.successSet_measurable ε)]
  exact integral_truthValue ν ((A.acceleratedLabelActualOutput_measurable hD z hn hk hL hε hμ hchain H)
    (F.successSet_measurable ε))

end Algorithm

theorem accelerated_finite_label_success_bound (n k H : ℕ) (hn : 10 ≤ n + 2) (hk : 0 < k)
    {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hchain : (n + 2 : ℝ) ^ 2 ≤ L / (4 * acceleratedSmoothnessConstant * μ)) (σ : ℝ)
    (hH : 2 * H + 2 ≤ acceleratedStageCount n k) {Seed : Type*} [MeasurableSpace Seed]
    (A : Algorithm (acceleratedLabelDimension n k H) (acceleratedLabelDimension n k H) Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (𝔼 z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin (acceleratedLabelDimension n k H),
      (A.outputLaw ν (FreshOracle.exact
        (acceleratedPhysicalModel (acceleratedPrimalLabelFrame (acceleratedLabelDimension_size n k H) z)
          (acceleratedDualLabelFrame (acceleratedLabelDimension_size n k H) z) hn hk hL hε hμ hchain) σ).kernel H).real
        ((acceleratedPhysicalModel (acceleratedPrimalLabelFrame (acceleratedLabelDimension_size n k H) z)
          (acceleratedDualLabelFrame (acceleratedLabelDimension_size n k H) z) hn hk hL hε hμ hchain).successSet ε)) ≤ (1 / 12 : ℝ) := by
  have hi := fun z => A.acceleratedLabelSuccessIndicator_integrable ν (acceleratedLabelDimension_size n k H)
    z hn hk hL hε hμ hchain H
  have hm := integral_mono (integrable_finite_average _ hi) (integrable_const (1 / 12 : ℝ))
    (A.acceleratedLabelSuccess_average n k H hn hk hL hε hμ hchain hH)
  rw [integral_finite_average _ hi] at hm
  have he (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin (acceleratedLabelDimension n k H)) :=
    A.acceleratedLabelSuccessIndicator_integral ν (acceleratedLabelDimension_size n k H) z hn hk hL hε hμ hchain σ H
  simp only [he] at hm
  simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using hm

end FreshGradientMinimax
