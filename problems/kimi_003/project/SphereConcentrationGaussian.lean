import HaarRebalancingUniform
import SLT.GaussianMeasure
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.ConditionalProbability

/-!
Concrete transfer of a normalized Gaussian annulus to the Haar unit-sphere
law. Its nonzero annulus mass is an explicit scalar hypothesis to be discharged
by the Gaussian radius estimate; no equality of these distributions is assumed.
-/

open Set MeasureTheory ProbabilityTheory
open Task006.HaarRebalancing
open scoped ENNReal NNReal ProbabilityTheory

namespace Task006.SphereConcentration
noncomputable section
variable {d : ℕ}

/-- The SLT Gaussian concentration measure is exactly Mathlib's standard
Euclidean Gaussian, rather than a Gaussian for the supremum norm. -/
theorem sltGaussian_eq_stdGaussian (d : ℕ) :
    GaussianMeasure.stdGaussianE d = stdGaussian (EuclideanSpace ℝ (Fin d)) := by
  change Measure.map (WithLp.toLp 2)
    (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) = _
  exact map_pi_eq_stdGaussian

/-- The closed outer annulus used to make radial normalization Lipschitz. -/
def outerAnnulus (d : ℕ) (r : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | r ≤ ‖x‖}

theorem measurableSet_outerAnnulus (d : ℕ) (r : ℝ) :
    MeasurableSet (outerAnnulus d r) :=
  (isClosed_le continuous_const continuous_norm).measurableSet

/-- The genuine Gaussian law conditioned on a radial annulus. -/
def gaussianAnnulusLaw (d : ℕ) (r : ℝ) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (stdGaussian (EuclideanSpace ℝ (Fin d)))[|outerAnnulus d r]

theorem gaussianAnnulusLaw_probability {r : ℝ}
    (hmass : stdGaussian (EuclideanSpace ℝ (Fin d)) (outerAnnulus d r) ≠ 0) :
    IsProbabilityMeasure (gaussianAnnulusLaw d r) :=
  cond_isProbabilityMeasure hmass

theorem measurable_normalize :
    Measurable (NormedSpace.normalize : EuclideanSpace ℝ (Fin d) → _) := by
  unfold NormedSpace.normalize
  exact measurable_norm.inv.smul measurable_id

/-- Conditioning on an actual radial set preserves Gaussian rotation
invariance, proved using the map/restrict identity. -/
theorem gaussianAnnulusLaw_rotationInvariant (r : ℝ)
    (U : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Measure.map U (gaussianAnnulusLaw d r) = gaussianAnnulusLaw d r := by
  have hpre : U ⁻¹' outerAnnulus d r = outerAnnulus d r := by
    ext x
    simp only [outerAnnulus, mem_preimage, mem_setOf_eq, U.norm_map]
  have hrestrict := Measure.restrict_map U.continuous.measurable
    (μ := stdGaussian (EuclideanSpace ℝ (Fin d))) (measurableSet_outerAnnulus d r)
  rw [stdGaussian_map, hpre] at hrestrict
  unfold gaussianAnnulusLaw ProbabilityTheory.cond
  rw [Measure.map_smul, ← hrestrict]

/-- The normalized direction under the actual conditioned Gaussian is
supported on the unit sphere and rotation invariant. -/
theorem gaussianAnnulusDirection_isUniform {r : ℝ} (hr : 0 < r) :
    UniformSphereLaw (NormedSpace.normalize : EuclideanSpace ℝ (Fin d) → _)
      (gaussianAnnulusLaw d r) := by
  refine ⟨measurable_normalize.aemeasurable, ?_, ?_⟩
  · apply ae_cond_of_forall_mem (measurableSet_outerAnnulus d r)
    intro x hx
    have hxpos : 0 < ‖x‖ := hr.trans_le hx
    exact NormedSpace.norm_normalize (norm_ne_zero_iff.mp hxpos.ne')
  · intro U
    have hcomm : (fun x : EuclideanSpace ℝ (Fin d) => U (NormedSpace.normalize x)) =
        NormedSpace.normalize ∘ U := by
      funext x
      simp [NormedSpace.normalize]
    rw [hcomm, ← Measure.map_map measurable_normalize U.continuous.measurable,
      gaussianAnnulusLaw_rotationInvariant]

/-- Equality to any concrete rotationally invariant unit-sphere law follows
from the proved Haar/Fubini uniqueness theorem. -/
theorem gaussianAnnulusDirection_map_eq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {v : Ω → EuclideanSpace ℝ (Fin d)} (hv : UniformSphereLaw v μ)
    {r : ℝ} (hr : 0 < r)
    (hmass : stdGaussian (EuclideanSpace ℝ (Fin d)) (outerAnnulus d r) ≠ 0) :
    Measure.map NormedSpace.normalize (gaussianAnnulusLaw d r) = Measure.map v μ := by
  letI : IsProbabilityMeasure (gaussianAnnulusLaw d r) := gaussianAnnulusLaw_probability hmass
  exact (gaussianAnnulusDirection_isUniform hr).map_eq hv

/-- In particular, the Gaussian direction is exactly the marginal law of
each column of the normalized Haar orthogonal matrix used by the algorithm. -/
theorem gaussianAnnulusDirection_eq_columnLaw (j : Fin d) {r : ℝ} (hr : 0 < r)
    (hmass : stdGaussian (EuclideanSpace ℝ (Fin d)) (outerAnnulus d r) ≠ 0) :
    Measure.map NormedSpace.normalize (gaussianAnnulusLaw d r) =
      Measure.map (fun Q : OrthogonalGroup d => column Q j) (orthogonalHaarProbability d) :=
  gaussianAnnulusDirection_map_eq (column_isUniform j) hr hmass

end
end Task006.SphereConcentration
