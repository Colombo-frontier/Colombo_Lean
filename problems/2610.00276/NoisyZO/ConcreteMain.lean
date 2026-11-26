import NoisyZO.LowerConcreteMinimax
import NoisyZO.GeneralMultiscaleAlgorithm

/-!
# Assumption-free normalized sharp-rate components

This file places the concrete adaptive lower bound and the concrete general
finite-smoothness upper construction under one statement.  Both use exactly
the saturated scale from the manuscript.  The lower side is a minimax theorem
for packaged fully adaptive Gaussian algorithms; the upper side is the output
law of the explicitly constructed projected multiscale method for every
normalized objective.

The purely order-theoretic step which turns matching lower and upper
certificates for a single common risk encoding into a minimax sandwich remains
`sharp_minimax_rate_of_certificates`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NoisyZO

noncomputable section

/-- The real-valued saturated rate shared by the concrete lower and upper
constructions. -/
def normalizedRateScaleReal (o : SmoothnessOrder) (d T : ℕ) : ℝ :=
  min 1 (((d : ℝ) ^ 2 / T) ^ rateExponent o.beta)

/-- The dimension- and budget-independent constant in the explicit adaptive
lower bound. -/
def dimensionFreeLowerRateConstant (o : SmoothnessOrder) : ℝ :=
  3 * (dimensionFreeRadialProfileData o).amplitude ^ 2 / 64

theorem dimensionFreeLowerRateConstant_pos (o : SmoothnessOrder) :
    0 < dimensionFreeLowerRateConstant o := by
  unfold dimensionFreeLowerRateConstant
  have ha := (dimensionFreeRadialProfileData o).amplitude_pos
  have haSq : 0 < (dimensionFreeRadialProfileData o).amplitude ^ 2 :=
    sq_pos_of_pos ha
  positivity

theorem fullMultiscaleRawRateConstant_pos (o : SmoothnessOrder) :
    0 < fullMultiscaleRawRateConstant o := by
  unfold fullMultiscaleRawRateConstant
  apply mul_pos
  · linarith [generalMultiscaleRateConstant_nonneg o]
  · have hqR : 0 < (fullMultiscaleRawCalls o : ℝ) := by
      exact_mod_cast fullMultiscaleRawCalls_pos o
    exact Real.rpow_pos_of_pos (by linarith) _

/-- The concrete minimax risk appearing in the assumption-free radial-family
lower bound. -/
def dimensionFreeConcreteMinimaxRisk
    {o : SmoothnessOrder} {alpha : Type*} [MeasurableSpace alpha]
    {d T : ℕ} (hd : 0 < d) (hT : 0 < T) (mu0 : Measure alpha) : ℝ≥0∞ :=
  minimaxRisk (fun A : AdaptiveGaussianAlgorithm alpha d ↦
    fun s : Hypercube d ↦
      ENNReal.ofReal
        (lowerRateAlgorithmRisk hd hT o.beta
          (dimensionFreeRadialProfileData o).amplitude o.beta_gt_two
          (dimensionFreeRadialProfileData o).amplitude_pos
          (dimensionFreeRadialProfileData o).amplitude_le_quarter mu0
          (dimensionFreeLowerRateQuantitativeCertificates hd hT) A s))

/-- The lower minimax result in the common real saturated-rate notation. -/
theorem dimensionFreeLowerRate_le_concreteMinimaxRisk
    {o : SmoothnessOrder} {alpha : Type*} [MeasurableSpace alpha]
    {d T : ℕ} (hd : 0 < d) (hT : 0 < T)
    (mu0 : Measure alpha) [IsProbabilityMeasure mu0] :
    ENNReal.ofReal
        (dimensionFreeLowerRateConstant o * normalizedRateScaleReal o d T) ≤
      dimensionFreeConcreteMinimaxRisk (o := o) hd hT mu0 := by
  simpa [dimensionFreeLowerRateConstant, normalizedRateScaleReal,
    dimensionFreeConcreteMinimaxRisk] using
      lowerRate_le_concrete_minimaxRisk_dimension_free
        (o := o) hd hT mu0

/-- Assumption-free matching-rate components for every fixed finite
smoothness order `beta > 2`, dimension, and positive raw-query budget.

The first inequality covers every packaged fully adaptive Gaussian algorithm.
The second clause supplies a probability output law and its uniform expected
optimization-gap bound for every normalized objective. -/
theorem normalized_sharp_rate_components
    {o : SmoothnessOrder} {alpha : Type*} [MeasurableSpace alpha]
    {d T : ℕ} (hd : 0 < d) (hT : 0 < T)
    (mu0 : Measure alpha) [IsProbabilityMeasure mu0] :
    0 < dimensionFreeLowerRateConstant o ∧
    0 < fullMultiscaleRawRateConstant o ∧
    ENNReal.ofReal
        (dimensionFreeLowerRateConstant o * normalizedRateScaleReal o d T) ≤
      dimensionFreeConcreteMinimaxRisk (o := o) hd hT mu0 ∧
    ∀ F : NormalizedObjective o d,
      IsProbabilityMeasure (fullMultiscaleProjectedBudgetOutputLaw F hd T) ∧
      (∫ x, F.f x - F.f F.minimizer
        ∂fullMultiscaleProjectedBudgetOutputLaw F hd T) ≤
        fullMultiscaleRawRateConstant o * normalizedRateScaleReal o d T := by
  refine ⟨dimensionFreeLowerRateConstant_pos o,
    fullMultiscaleRawRateConstant_pos o, ?_, ?_⟩
  · exact dimensionFreeLowerRate_le_concreteMinimaxRisk hd hT mu0
  · intro F
    constructor
    · exact fullMultiscaleProjectedBudgetOutputLaw_isProbability F hd T hT
    · simpa only [normalizedRateScaleReal] using
        F.fullMultiscaleProjectedBudgetOutputLaw_saturated_rate hd T hT

end

end NoisyZO
