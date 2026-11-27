import Nonsmooth.FiniteSupport
import Nonsmooth.FiniteSampling
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ConditionalProbability

open MeasureTheory ProbabilityTheory Metric Filter Function
open scoped Topology InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def standardGaussianCoordinates (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance standardGaussianCoordinates_probability (d : ℕ) : IsProbabilityMeasure (standardGaussianCoordinates d) := by
  unfold standardGaussianCoordinates
  infer_instance

instance standardGaussianReal_openPositive : Measure.IsOpenPosMeasure (gaussianReal 0 1) :=
  (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : NNReal) ≠ 0)).isOpenPosMeasure

instance standardGaussianCoordinates_openPositive (d : ℕ) : Measure.IsOpenPosMeasure (standardGaussianCoordinates d) := by
  unfold standardGaussianCoordinates
  infer_instance

def gaussianSynthesis (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (v : Fin (Module.finrank ℝ E) → ℝ) : E :=
  ∑ i, v i • stdOrthonormalBasis ℝ E i

theorem gaussianSynthesis_continuous : Continuous (gaussianSynthesis E) := by
  unfold gaussianSynthesis
  exact continuous_finsetSum _ (fun i _ => (continuous_apply i).smul continuous_const)

theorem gaussianSynthesis_surjective : Surjective (gaussianSynthesis E) := by
  intro z
  exact ⟨fun i => ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ, (stdOrthonormalBasis ℝ E).sum_repr' z⟩

theorem gaussianSynthesis_coordinate (v : Fin (Module.finrank ℝ E) → ℝ)
    (i : Fin (Module.finrank ℝ E)) : ⟪stdOrthonormalBasis ℝ E i, gaussianSynthesis E v⟫_ℝ = v i := by
  simp only [gaussianSynthesis, inner_sum, inner_smul_right,
    (orthonormal_iff_ite.mp (stdOrthonormalBasis ℝ E).orthonormal)]
  simp

/-- The actual standard Gaussian vector: independent N(0,1) coordinates in a fixed
orthonormal basis. No hardness probability is assumed by this definition. -/
def euclideanGaussianLaw (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] : Measure E :=
  Measure.map (gaussianSynthesis E) (standardGaussianCoordinates (Module.finrank ℝ E))

instance euclideanGaussianLaw_probability : IsProbabilityMeasure (euclideanGaussianLaw E) := by
  unfold euclideanGaussianLaw
  exact Measure.isProbabilityMeasure_map gaussianSynthesis_continuous.measurable.aemeasurable

instance euclideanGaussianLaw_openPositive : Measure.IsOpenPosMeasure (euclideanGaussianLaw E) :=
  gaussianSynthesis_continuous.isOpenPosMeasure_map gaussianSynthesis_surjective

theorem euclideanGaussianLaw_coordinate (i : Fin (Module.finrank ℝ E)) :
    Measure.map (fun z : E => ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ) (euclideanGaussianLaw E) = gaussianReal 0 1 := by
  have hm : Measurable (fun z : E => ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ) :=
    (continuous_const.inner continuous_id).measurable
  rw [euclideanGaussianLaw, Measure.map_map hm gaussianSynthesis_continuous.measurable]
  simpa only [Function.comp_def, gaussianSynthesis_coordinate, standardGaussianCoordinates] using
    (finite_product_coordinate (gaussianReal 0 1) i).map_eq

theorem euclideanGaussianLaw_truncation_positive :
    0 < euclideanGaussianLaw E (closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E))) := by
  have hr : 0 < 2 * Real.sqrt (Module.finrank ℝ E : ℝ) := by
    exact mul_pos (by norm_num) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos))
  exact (measure_ball_pos (euclideanGaussianLaw E) (0 : E) hr).trans_le (measure_mono ball_subset_closedBall)

def truncatedGaussianLaw (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] : Measure E :=
  (euclideanGaussianLaw E)[|closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E))]

instance truncatedGaussianLaw_probability : IsProbabilityMeasure (truncatedGaussianLaw E) :=
  cond_isProbabilityMeasure euclideanGaussianLaw_truncation_positive.ne'

theorem truncatedGaussianLaw_supported :
    ∀ᵐ z ∂truncatedGaussianLaw E, ‖z‖ ≤ 2 * Real.sqrt (Module.finrank ℝ E) := by
  have h : ∀ᵐ z ∂(euclideanGaussianLaw E).restrict
      (closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E))),
      ‖z‖ ≤ 2 * Real.sqrt (Module.finrank ℝ E) := by
    simpa only [mem_closedBall, dist_zero_right] using
      ae_restrict_mem (μ := euclideanGaussianLaw E)
        (s := closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E))) measurableSet_closedBall
  exact Measure.ae_smul_measure h _

def truncatedGaussianVectorLaw (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] :
    Measure (Feasible E (2 * Real.sqrt (Module.finrank ℝ E))) :=
  (truncatedGaussianLaw E).comap Subtype.val

instance truncatedGaussianVectorLaw_probability : IsProbabilityMeasure (truncatedGaussianVectorLaw E) := by
  have he : MeasurableEmbedding (Subtype.val : Feasible E (2 * Real.sqrt (Module.finrank ℝ E)) → E) :=
    MeasurableEmbedding.subtype_coe (isClosed_le continuous_norm continuous_const).measurableSet
  apply he.isProbabilityMeasure_comap
  filter_upwards [truncatedGaussianLaw_supported (E := E)] with z hz
  exact ⟨⟨z, hz⟩, rfl⟩

theorem truncatedGaussianVectorLaw_integral (f : E → ℝ) :
    (∫ z : Feasible E (2 * Real.sqrt (Module.finrank ℝ E)), f z.val ∂truncatedGaussianVectorLaw E) =
      ∫ z : E, f z ∂truncatedGaussianLaw E := by
  rw [truncatedGaussianVectorLaw]
  erw [integral_subtype_comap (μ := truncatedGaussianLaw E)
    (s := {z : E | ‖z‖ ≤ 2 * Real.sqrt (Module.finrank ℝ E)})
    (isClosed_le continuous_norm continuous_const).measurableSet f]
  erw [Measure.restrict_eq_self_of_ae_mem (truncatedGaussianLaw_supported (E := E))]

def gaussianScaleRow (z : Feasible E (2 * Real.sqrt (Module.finrank ℝ E))) : Feasible E 2 :=
  rescaledSupportRows (ι := Unit) Module.finrank_pos (fun _ => z) ()

theorem gaussianScaleRow_measurable : Measurable (gaussianScaleRow (E := E)) :=
  (measurable_const.smul measurable_subtype_coe).subtype_mk

theorem gaussianScaleRow_value (z : Feasible E (2 * Real.sqrt (Module.finrank ℝ E))) :
    (gaussianScaleRow z).val = (Real.sqrt (Module.finrank ℝ E))⁻¹ • z.val := rfl

def gaussianSupportRowLaw (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] : Measure (Feasible E 2) :=
  Measure.map gaussianScaleRow (truncatedGaussianVectorLaw E)

instance gaussianSupportRowLaw_probability : IsProbabilityMeasure (gaussianSupportRowLaw E) :=
  Measure.isProbabilityMeasure_map gaussianScaleRow_measurable.aemeasurable

/-- The manuscript's fixed, independent truncated Gaussian row prior, defined before
any query policy or budget. The two remaining hardness events are not asserted here. -/
def gaussianSupportPrior (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] (k : ℕ) :
    Measure (BoundedSupportRows E (Fin k)) := Measure.pi (fun _ => gaussianSupportRowLaw E)

instance gaussianSupportPrior_probability (k : ℕ) : IsProbabilityMeasure (gaussianSupportPrior E k) := by
  constructor
  change Measure.pi (fun _ : Fin k => gaussianSupportRowLaw E) Set.univ = 1
  rw [Measure.pi_univ]
  simp

theorem gaussianSupportPrior_coordinate {k : ℕ} (i : Fin k) :
    MeasurePreserving (fun a : BoundedSupportRows E (Fin k) => a i)
      (gaussianSupportPrior E k) (gaussianSupportRowLaw E) :=
  finite_product_coordinate (gaussianSupportRowLaw E) i

theorem gaussianSupportPrior_independent (k : ℕ) :
    iIndepFun (fun i (a : BoundedSupportRows E (Fin k)) => a i) (gaussianSupportPrior E k) :=
  finite_product_independent (gaussianSupportRowLaw E) k

theorem gaussianSupportPrior_model {k : ℕ} (hk : 0 < k) :
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    ∀ᵐ a ∂gaussianSupportPrior E k, SupportModel (boundedFiniteSupport a) := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  exact Eventually.of_forall boundedFiniteSupport_model

end
end Nonsmooth
