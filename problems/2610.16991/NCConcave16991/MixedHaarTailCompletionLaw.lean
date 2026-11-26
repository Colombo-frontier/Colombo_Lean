import NCConcave16991.MixedHaarTargetedCompletionLaw
import NCConcave16991.MixedHaarProbabilityTransport

/-! # Reparameterizing the one-step inverse kernel by a genuine smaller Haar group -/

noncomputable section

open Set MeasureTheory ProbabilityTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000

attribute [local irreducible] sphereSelector projectedSample projectedInverseCompletion
  targetedProjectedInverseCompletion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {k m : ℕ}

def tailTargetedInverseCompletion (D : Submodule ℝ E) (U : D ≃ₗᵢ[ℝ] SphereSpace k)
    (e₀ e : SphereSpace k) (f : Haar.OrthogonalGroup m →* pointStabilizer e₀)
    (p : E × Haar.OrthogonalGroup m) : Haar.OrthogonalGroup k :=
  targetedProjectedInverseCompletion D U e₀ e (p.1,f p.2)

theorem tail_completion_source_preserving (e₀ : SphereSpace k)
    (f : Haar.OrthogonalGroup m →* pointStabilizer e₀) (hf : Continuous f)
    (hsurj : Function.Surjective f) :
    MeasurePreserving (Prod.map (id : E → E) f)
      ((stdGaussian E).prod (Haar.haarLaw m)) ((stdGaussian E).prod (pointStabilizerLaw e₀)) :=
  (MeasurePreserving.id (stdGaussian E)).prod (pointStabilizerHaar_transport e₀ f hf hsurj)

theorem tailTargetedInverseCompletion_preserving (D : Submodule ℝ E)
    (U : D ≃ₗᵢ[ℝ] SphereSpace k) (e₀ : SphereSpace k) (he₀ : ‖e₀‖ = 1) (e : SphereSpace k)
    (f : Haar.OrthogonalGroup m →* pointStabilizer e₀) (hf : Continuous f)
    (hsurj : Function.Surjective f) :
    MeasurePreserving (tailTargetedInverseCompletion D U e₀ e f)
      ((stdGaussian E).prod (Haar.haarLaw m)) (Haar.haarLaw k) := by
  exact (targetedProjectedInverseCompletion_preserving D U e₀ he₀ e).comp
    (tail_completion_source_preserving e₀ f hf hsurj)

/-- The exact local joint law now uses only fixed-dimensional standard
Gaussian and ordinary orthogonal Haar sources, with no subgroup-law premise. -/
theorem tailTargetedInverseCompletion_jointLaw (D : Submodule ℝ E)
    (U : D ≃ₗᵢ[ℝ] SphereSpace k) (e₀ e : SphereSpace k) (he₀ : ‖e₀‖ = 1) (he : ‖e‖ = 1)
    (f : Haar.OrthogonalGroup m →* pointStabilizer e₀) (hf : Continuous f)
    (hsurj : Function.Surjective f) :
    ((stdGaussian E).prod (Haar.haarLaw m)).map
        (fun p ↦ (projectedSample D U p.1,tailTargetedInverseCompletion D U e₀ e f p)) =
      (Haar.haarLaw k).map (fun Q ↦ (Haar.orthogonalLinearIsometryEquiv Q⁻¹ e,Q)) := by
  have hs := tail_completion_source_preserving (E := E) e₀ f hf hsurj
  let pair := fun p : E × pointStabilizer e₀ ↦
    (projectedSample D U p.1,targetedProjectedInverseCompletion D U e₀ e p)
  have hp : Measurable pair := ((projectedSample_measurable D U).comp measurable_fst).prodMk
    (targetedProjectedInverseCompletion_preserving D U e₀ he₀ e).measurable
  have hlaw := congrArg (fun μ : Measure (E × pointStabilizer e₀) ↦ μ.map pair) hs.map_eq
  rw [Measure.map_map hp hs.measurable] at hlaw
  calc
    _ = ((stdGaussian E).prod (pointStabilizerLaw e₀)).map pair := by
      simpa only [Function.comp_def,pair,Prod.map,id_eq,tailTargetedInverseCompletion] using hlaw
    _ = _ := targetedProjectedInverseCompletion_jointLaw D U e₀ e he₀ he

theorem tailTargetedInverseCompletion_joint_measurable (D : Submodule ℝ E)
    (U : D ≃ₗᵢ[ℝ] SphereSpace k) (e₀ : SphereSpace k) (he₀ : ‖e₀‖ = 1)
    (f : Haar.OrthogonalGroup m →* pointStabilizer e₀) (hf : Continuous f) :
    Measurable (fun p : SphereSpace k × (E × Haar.OrthogonalGroup m) ↦
      tailTargetedInverseCompletion D U e₀ p.1 f p.2) := by
  have hm : Measurable (fun p : SphereSpace k × (E × Haar.OrthogonalGroup m) ↦
      (p.1,(p.2.1,f p.2.2))) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (hf.measurable.comp (measurable_snd.comp measurable_snd)))
  exact (targetedProjectedInverseCompletion_joint_measurable D U e₀ he₀).comp hm

end NCConcave16991.MixedHaar
