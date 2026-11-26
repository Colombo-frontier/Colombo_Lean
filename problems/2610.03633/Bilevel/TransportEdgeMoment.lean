import Bilevel.TransportEdgePosterior
import Bilevel.TransportObserverIsotropicMoment

/-! Residual conditional edge isotropy yields the actual fresh-image Frobenius
moment. Perpendicular support is kept explicit for the paired-action history
to discharge; the moment or probability conclusion is not assumed. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.TransportEdgePosterior
open EuclideanGaussian OrthogonalAction ProjectionGeometry TransportObserver
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 400000

def images {D r : ℕ} (v : Fin r → Space D) (O : OrthogonalHaar.Group D) :
    ProjectionPosterior.Frame D r := fun i => O • v i

theorem images_measurable {D r : ℕ} (v : Fin r → Space D) : Measurable (images v) :=
  measurable_pi_lambda _ (fun _ => measurable_id.smul measurable_const)

theorem images_invariant {D r : ℕ} (B : Submodule ℝ (Space D))
    (μ : Measure (OrthogonalHaar.Group D)) (hμ : Invariant B μ) (v : Fin r → Space D) :
    ProjectionPosterior.Invariant D r B (μ.map (images v)) := by
  intro S
  apply ConditionalSymmetry.pushforward_preserving μ (images v) (images_measurable v)
    (fun O => S.val*O) (fun U : ProjectionPosterior.Frame D r => S • U)
    (hμ S) (measurable_const.smul measurable_id)
  intro O
  funext i
  exact mul_smul S.val O (v i)

theorem images_norm_ae {D r : ℕ} (μ : Measure (OrthogonalHaar.Group D))
    (v : Fin r → Space D) (hv : ∀ i, ‖v i‖ = 1) :
    ∀ᵐ U ∂μ.map (images v), ∀ i, ‖U i‖ ≤ 1 := by
  apply (ae_map_iff (images_measurable v).aemeasurable
    (show MeasurableSet {U : ProjectionPosterior.Frame D r | ∀ i, ‖U i‖ ≤ 1} from by
      simp only [Set.setOf_forall]
      exact MeasurableSet.iInter (fun i => measurableSet_le (measurable_pi_apply i).norm measurable_const))).mpr
  apply Filter.Eventually.of_forall
  intro O i
  change ‖(isometry D O) (v i)‖ ≤ 1
  simp only [LinearIsometryEquiv.norm_map,hv i,le_refl]

theorem images_perpendicular_ae {D r : ℕ} (B : Submodule ℝ (Space D))
    (μ : Measure (OrthogonalHaar.Group D)) (v : Fin r → Space D)
    (hp : ∀ᵐ O ∂μ, ∀ i, O • v i ∈ Bᗮ) :
    ∀ᵐ U ∂μ.map (images v), ∀ i, U i ∈ Bᗮ := by
  apply (ae_map_iff (images_measurable v).aemeasurable
    (show MeasurableSet {U : ProjectionPosterior.Frame D r | ∀ i, U i ∈ Bᗮ} from by
      simp only [Set.setOf_forall]
      exact MeasurableSet.iInter (fun i => (measurable_pi_apply i) B.isClosed_orthogonal.measurableSet))).mpr
  exact hp

theorem images_energy_integrable {D r : ℕ} (W : Submodule ℝ (Space D))
    (μ : Measure (OrthogonalHaar.Group D)) [IsProbabilityMeasure μ]
    (v : Fin r → Space D) (hv : ∀ i, ‖v i‖ = 1) :
    Integrable (fun O => frameEnergy W (images v O) Finset.univ) μ := by
  letI : IsProbabilityMeasure (μ.map (images v)) := isProbabilityMeasure_map (images_measurable v).aemeasurable
  have hi : Integrable (fun U : ProjectionPosterior.Frame D r => frameEnergy W U Finset.univ)
      (μ.map (images v)) := by
    unfold frameEnergy
    apply integrable_finset_sum
    intro i _
    simp_rw [projection_energy_parseval W (stdOrthonormalBasis ℝ W)]
    exact integrable_finset_sum _ (fun j _ => invariant_query_integrable D r _
      (images_norm_ae μ v hv) ((stdOrthonormalBasis ℝ W) j : Space D) i)
  exact hi.comp_measurable (images_measurable v)

theorem images_energy_moment {D r : ℕ} (B W : Submodule ℝ (Space D))
    (hd : 0 < Module.finrank ℝ Bᗮ)
    (μ : Measure (OrthogonalHaar.Group D)) [IsProbabilityMeasure μ] (hμ : Invariant B μ)
    (v : Fin r → Space D) (hv : ∀ i, ‖v i‖ = 1)
    (hp : ∀ᵐ O ∂μ, ∀ i, O • v i ∈ Bᗮ) :
    (∫ O, frameEnergy W (images v O) Finset.univ ∂μ) ≤
      (r:ℝ)*Module.finrank ℝ W/(Module.finrank ℝ Bᗮ : ℝ) := by
  letI : IsProbabilityMeasure (μ.map (images v)) := isProbabilityMeasure_map (images_measurable v).aemeasurable
  have hh := invariant_supported_frame_moment D r B W (stdOrthonormalBasis ℝ Bᗮ)
    (stdOrthonormalBasis ℝ W) (by simpa only [Fintype.card_fin] using hd)
    (μ.map (images v)) (images_invariant B μ hμ v) (images_norm_ae μ v hv)
    (images_perpendicular_ae B μ v hp)
  have hm : Measurable (fun U : ProjectionPosterior.Frame D r => frameEnergy W U Finset.univ) := by
    unfold frameEnergy
    apply Finset.measurable_sum
    intro i _
    simp_rw [projection_energy_parseval W (stdOrthonormalBasis ℝ W)]
    exact Finset.measurable_sum _ (fun j _ =>
      ((continuous_const.inner (continuous_apply i)).pow 2).measurable)
  rw [integral_map (images_measurable v).aemeasurable hm.aestronglyMeasurable] at hh
  simpa only [Fintype.card_fin] using hh

theorem images_projection_failure {D r : ℕ} (B W : Submodule ℝ (Space D))
    (hd : 0 < Module.finrank ℝ Bᗮ)
    (μ : Measure (OrthogonalHaar.Group D)) [IsProbabilityMeasure μ] (hμ : Invariant B μ)
    (v : Fin r → Space D) (hv : ∀ i, ‖v i‖ = 1)
    (hp : ∀ᵐ O ∂μ, ∀ i, O • v i ∈ Bᗮ) :
    μ.real {O | (1:ℝ)/64 < frameEnergy W (images v O) Finset.univ} ≤
      64*((r:ℝ)*Module.finrank ℝ W/(Module.finrank ℝ Bᗮ : ℝ)) :=
  fresh_projection_failure_of_moment μ _
    (fun O => frameEnergy_nonneg W (images v O) Finset.univ)
    (images_energy_integrable W μ v hv) (images_energy_moment B W hd μ hμ v hv hp)

end Bilevel.TransportEdgePosterior
