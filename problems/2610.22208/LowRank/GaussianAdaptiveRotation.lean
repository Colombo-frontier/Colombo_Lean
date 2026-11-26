import LowRank.GaussianOrthogonal
import Mathlib.MeasureTheory.Measure.Prod

/-! Rotating an independent hidden Gaussian by a measurable function of the
already exposed state preserves its joint product law. The measurable family
of rotations must be constructed before this theorem can be applied. -/

namespace LowRank
open MeasureTheory ProbabilityTheory

variable {S E : Type*} [MeasurableSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem state_dependent_gaussian_rotation {ν : Measure S} [SFinite ν]
    (e : S → E ≃ₗᵢ[ℝ] E)
    (he : Measurable (fun p : S × E => e p.1 p.2)) :
    (ν.prod (euclideanGaussianLaw E)).map
      (fun p : S × E => (p.1, e p.1 p.2)) = ν.prod (euclideanGaussianLaw E) := by
  have h := (MeasurePreserving.id ν).skew_product he
    (Filter.Eventually.of_forall (fun s => euclideanGaussian_isometry E (e s)))
  exact h.map_eq

/-- The same joint-law conclusion for a state and hidden Gaussian living on an
arbitrary underlying probability space, once their product law has been proved. -/
theorem hidden_gaussian_rotation_joint_law
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ν : Measure S} [SFinite ν] (state : Ω → S) (hidden : Ω → E)
    (hj : Measurable (fun ω => (state ω, hidden ω)))
    (hlaw : μ.map (fun ω => (state ω, hidden ω)) = ν.prod (euclideanGaussianLaw E))
    (e : S → E ≃ₗᵢ[ℝ] E)
    (he : Measurable (fun p : S × E => e p.1 p.2)) :
    μ.map (fun ω => (state ω, e (state ω) (hidden ω))) = ν.prod (euclideanGaussianLaw E) := by
  have hm : Measurable (fun p : S × E => (p.1, e p.1 p.2)) := measurable_fst.prodMk he
  have h := state_dependent_gaussian_rotation (ν := ν) e he
  rw [← hlaw, Measure.map_map hm hj] at h
  exact h.trans hlaw

end LowRank
