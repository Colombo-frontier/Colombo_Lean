import FreshGradientMinimax.LabelSuccess
import FreshGradientMinimax.FiniteEventIntegral

/-! The finite hard distribution against arbitrary measurable randomized
algorithms. The seed space is arbitrary; only a probability law is required. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory
open scoped BigOperators

namespace Algorithm
variable {D : ℕ} {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm 1 D Seed)

theorem labelActualOutput_measurable (p : Parameters) (hκ : 4 * p.μ ≤ p.L) (N : ℕ)
    (hD : 4 * N + 4 ≤ D) (z : Fin (4 * N + 4) → Fin D) (s : ℝ) (hs : s ^ 2 = 1) :
    Measurable (A.labelActualOutput p hκ N hD z s hs) :=
  (A.output_measurable N).comp (A.deterministicRun_measurable _
    (fun _ => (pathHorizonObjective p hκ N (labelFrame hD z) s hs).jointGradient_continuous.measurable) N)

theorem labelSuccessIndicator_integrable (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p : Parameters) (hκ : 4 * p.μ ≤ p.L) (N : ℕ) (hD : 4 * N + 4 ≤ D)
    (z : Fin (4 * N + 4) → Fin D) (s : ℝ) (hs : s ^ 2 = 1) :
    Integrable (A.labelSuccessIndicator p hκ N hD z s hs) ν :=
  truthValue_integrable ν ((A.labelActualOutput_measurable p hκ N hD z s hs)
    ((pathHorizonObjective p hκ N (labelFrame hD z) s hs).successSet_measurable p.ε))

theorem labelSuccessIndicator_integral (ν : Measure Seed) (p : Parameters)
    (hκ : 4 * p.μ ≤ p.L) (N : ℕ) (hD : 4 * N + 4 ≤ D)
    (z : Fin (4 * N + 4) → Fin D) (s : ℝ) (hs : s ^ 2 = 1) :
    (∫ seed, A.labelSuccessIndicator p hκ N hD z s hs seed ∂ν) =
      (A.outputLaw ν (FreshOracle.exact (pathHorizonObjective p hκ N (labelFrame hD z) s hs) p.σ).kernel N).real
        ((pathHorizonObjective p hκ N (labelFrame hD z) s hs).successSet p.ε) := by
  let F := pathHorizonObjective p hκ N (labelFrame hD z) s hs
  change (∫ seed, A.labelSuccessIndicator p hκ N hD z s hs seed ∂ν) =
    (A.outputLaw ν (ProbabilityTheory.Kernel.deterministic F.jointGradient
      F.jointGradient_continuous.measurable) N).real (F.successSet p.ε)
  rw [A.outputLaw_exact ν F.jointGradient_continuous.measurable N]
  change (∫ seed, A.labelSuccessIndicator p hκ N hD z s hs seed ∂ν) =
    (ν.map (A.labelActualOutput p hκ N hD z s hs)).real (F.successSet p.ε)
  rw [Measure.real, Measure.map_apply (A.labelActualOutput_measurable p hκ N hD z s hs)
      (F.successSet_measurable p.ε)]
  exact integral_truthValue ν ((A.labelActualOutput_measurable p hκ N hD z s hs) (F.successSet_measurable p.ε))

theorem labelPairSuccess_integrable (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p : Parameters) (hκ : 4 * p.μ ≤ p.L) (N : ℕ) (hD : 4 * N + 4 ≤ D)
    (z : Fin (4 * N + 4) → Fin D) : Integrable (A.labelPairSuccess p hκ N hD z) ν :=
  ((A.labelSuccessIndicator_integrable ν p hκ N hD z 1 (by norm_num)).add
    (A.labelSuccessIndicator_integrable ν p hκ N hD z (-1) (by norm_num))).div_const 2

theorem labelPairSuccess_integral (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p : Parameters) (hκ : 4 * p.μ ≤ p.L) (N : ℕ) (hD : 4 * N + 4 ≤ D)
    (z : Fin (4 * N + 4) → Fin D) :
    (∫ seed, A.labelPairSuccess p hκ N hD z seed ∂ν) =
      ((A.outputLaw ν (FreshOracle.exact (pathHorizonObjective p hκ N (labelFrame hD z) 1 (by norm_num)) p.σ).kernel N).real
          ((pathHorizonObjective p hκ N (labelFrame hD z) 1 (by norm_num)).successSet p.ε) +
        (A.outputLaw ν (FreshOracle.exact (pathHorizonObjective p hκ N (labelFrame hD z) (-1) (by norm_num)) p.σ).kernel N).real
          ((pathHorizonObjective p hκ N (labelFrame hD z) (-1) (by norm_num)).successSet p.ε)) / 2 := by
  unfold labelPairSuccess
  rw [integral_div, integral_add (A.labelSuccessIndicator_integrable ν p hκ N hD z 1 (by norm_num))
    (A.labelSuccessIndicator_integrable ν p hκ N hD z (-1) (by norm_num)),
    A.labelSuccessIndicator_integral, A.labelSuccessIndicator_integral]

end Algorithm

def labelAverageSuccess (p : Parameters) (hκ : 4 * p.μ ≤ p.L) (N : ℕ)
    (A : RandomizedAlgorithm 1 (labelHidingDimension p N)) : ℝ :=
  𝔼 z : Fin (4 * N + 4) → Fin (labelHidingDimension p N),
    ((A.outputLaw (FreshOracle.exact
      (pathHorizonObjective p hκ N (labelFrame (labelHidingDimension_size p N) z) 1 (by norm_num)) p.σ).kernel N).real
        ((pathHorizonObjective p hκ N (labelFrame (labelHidingDimension_size p N) z) 1 (by norm_num)).successSet p.ε) +
      (A.outputLaw (FreshOracle.exact
      (pathHorizonObjective p hκ N (labelFrame (labelHidingDimension_size p N) z) (-1) (by norm_num)) p.σ).kernel N).real
        ((pathHorizonObjective p hκ N (labelFrame (labelHidingDimension_size p N) z) (-1) (by norm_num)).successSet p.ε)) / 2

theorem label_distribution_success_bound (p : Parameters) (hκ : 4 * p.μ ≤ p.L) (N : ℕ)
    (A : RandomizedAlgorithm 1 (labelHidingDimension p N)) : labelAverageSuccess p hκ N A ≤ (7 / 12 : ℝ) := by
  have hi := A.policy.labelPairSuccess_integrable A.seedLaw p hκ N (labelHidingDimension_size p N)
  have he := integral_finite_average
    (fun z => A.policy.labelPairSuccess p hκ N (labelHidingDimension_size p N) z) hi
  have hm := integral_mono (integrable_finite_average _ hi) (integrable_const (7 / 12 : ℝ))
    (A.policy.labelPairSuccess_average p hκ N)
  rw [he] at hm
  simp only [A.policy.labelPairSuccess_integral] at hm
  simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using hm

end FreshGradientMinimax
