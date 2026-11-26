import GradientHessian.GaussianConcentrationProductIBP
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-! Gaussian integration by parts in the actual Euclidean Hilbert space.
Coordinates are those defining the law; the derivative is the actual Fréchet
derivative, with integrability hypotheses specifying the allowed growth. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory ProbabilityTheory GaussianHilbert GaussianSquare
open scoped InnerProductSpace

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem gaussianSynthesis_update (v : Fin (Module.finrank ℝ E) → ℝ)
    (i : Fin (Module.finrank ℝ E)) (t : ℝ) :
    gaussianSynthesis E (Function.update v i t) =
      gaussianSynthesis E v + (t - v i) • stdOrthonormalBasis ℝ E i := by
  apply (stdOrthonormalBasis ℝ E).repr.injective
  ext j
  simp only [OrthonormalBasis.repr_apply_apply, gaussianSynthesis_coordinate,
    inner_add_right, inner_smul_right,
    orthonormal_iff_ite.mp (stdOrthonormalBasis ℝ E).orthonormal]
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

omit [MeasurableSpace E] [BorelSpace E] in
theorem gaussianSynthesis_update_hasDerivAt (v : Fin (Module.finrank ℝ E) → ℝ)
    (i : Fin (Module.finrank ℝ E)) (t : ℝ) :
    HasDerivAt (fun s => gaussianSynthesis E (Function.update v i s))
      (stdOrthonormalBasis ℝ E i) t := by
  have he : (fun s => gaussianSynthesis E (Function.update v i s)) =
      fun s => gaussianSynthesis E v + (s - v i) • stdOrthonormalBasis ℝ E i :=
    funext (gaussianSynthesis_update E v i)
  rw [he]
  simpa only [one_smul] using
    (((hasDerivAt_id t).sub_const (v i)).smul_const (stdOrthonormalBasis ℝ E i)).const_add
      (gaussianSynthesis E v)

theorem hilbert_gaussian_integration_by_parts (i : Fin (Module.finrank ℝ E))
    {f : E → ℝ} (hf : Differentiable ℝ f)
    (hI : Integrable f (euclideanGaussianLaw E))
    (hD : Integrable (fun z => fderiv ℝ f z (stdOrthonormalBasis ℝ E i))
      (euclideanGaussianLaw E))
    (hX : Integrable (fun z => ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ * f z)
      (euclideanGaussianLaw E)) :
    (∫ z, ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ * f z ∂euclideanGaussianLaw E) =
      ∫ z, fderiv ℝ f z (stdOrthonormalBasis ℝ E i) ∂euclideanGaussianLaw E := by
  have hsm : AEMeasurable (gaussianSynthesis E) (gaussianVector (Module.finrank ℝ E)) :=
    (gaussianSynthesis_continuous E).measurable.aemeasurable
  have hfi : Integrable (fun v => f (gaussianSynthesis E v))
      (gaussianVector (Module.finrank ℝ E)) :=
    (integrable_map_measure hI.aestronglyMeasurable hsm).mp hI
  have hdi : Integrable (fun v => fderiv ℝ f (gaussianSynthesis E v) (stdOrthonormalBasis ℝ E i))
      (gaussianVector (Module.finrank ℝ E)) :=
    (integrable_map_measure hD.aestronglyMeasurable hsm).mp hD
  have hxi : Integrable (fun v => v i * f (gaussianSynthesis E v))
      (gaussianVector (Module.finrank ℝ E)) := by
    have hi := (integrable_map_measure hX.aestronglyMeasurable hsm).mp hX
    change Integrable (fun v => ⟪stdOrthonormalBasis ℝ E i, gaussianSynthesis E v⟫_ℝ *
      f (gaussianSynthesis E v)) _ at hi
    simpa only [gaussianSynthesis_coordinate] using hi
  have hd (v : Fin (Module.finrank ℝ E) → ℝ) :
      HasDerivAt (fun s => f (gaussianSynthesis E (Function.update v i s)))
        (fderiv ℝ f (gaussianSynthesis E v) (stdOrthonormalBasis ℝ E i)) (v i) := by
    have h := (hf (gaussianSynthesis E (Function.update v i (v i)))).hasFDerivAt.comp_hasDerivAt
      (v i) (gaussianSynthesis_update_hasDerivAt E v i (v i))
    simpa only [Function.update_eq_self] using h
  have hi := gaussian_partial_integration_by_parts i hd hfi hdi hxi
  rw [euclideanGaussianLaw, integral_map hsm hX.aestronglyMeasurable,
    integral_map hsm hD.aestronglyMeasurable]
  simpa only [gaussianSynthesis_coordinate] using hi

end GradientHessian.GaussianConcentration
