import Nonsmooth.SupportPosteriorKernel
import Nonsmooth.GaussianSpectralBridge

open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  {k : ℕ} [Nonempty (Fin k)] {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]

theorem gaussianAmbientRowLaw_norm_le_two : ∀ᵐ a : E ∂gaussianAmbientRowLaw E, ‖a‖ ≤ 2 := by
  rw [gaussianAmbientRowLaw]
  exact (ae_map_iff measurable_subtype_coe.aemeasurable
    (measurableSet_le continuous_norm.measurable measurable_const)).mpr
      (Eventually.of_forall (fun a => a.property))

theorem gaussianAmbientRowLaw_memLp : MemLp (fun a : E => a) 2 (gaussianAmbientRowLaw E) :=
  MemLp.of_bound measurable_id.aestronglyMeasurable 2 gaussianAmbientRowLaw_norm_le_two

theorem gaussianAmbientRowLaw_mean_zero : (∫ a : E, a ∂gaussianAmbientRowLaw E) = 0 := by
  let e : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.neg ℝ
  have hp : MeasurePreserving e (gaussianAmbientRowLaw E) (gaussianAmbientRowLaw E) :=
    ⟨e.continuous.measurable, gaussianAmbientRowLaw_isometry e⟩
  have h := hp.integral_comp e.toMeasurableEquiv.measurableEmbedding (fun a : E => a)
  change (∫ a : E, -a ∂gaussianAmbientRowLaw E) = ∫ a : E, a ∂gaussianAmbientRowLaw E at h
  rw [integral_neg] at h
  have hz : (2 : ℝ) • (∫ a : E, a ∂gaussianAmbientRowLaw E) = 0 := by
    rw [two_smul]
    exact neg_eq_iff_add_eq_zero.mp h
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

theorem gaussianAmbientRows_coordinate_memLp (i : Fin k) :
    MemLp (fun a : Fin k → E => a i) 2 (Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) := by
  exact (gaussianAmbientRowLaw_memLp (E := E)).comp_measurePreserving
    (finite_product_coordinate (gaussianAmbientRowLaw E) i)

theorem gaussianAmbientRows_aggregate_integrable :
    Integrable (fun a : Fin k → E => ∑ i, a i) (Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) := by
  exact integrable_finset_sum _ (fun i _ => (gaussianAmbientRows_coordinate_memLp i).integrable (by norm_num))

theorem gaussianAmbientRows_aggregate_mean_zero :
    (∫ a : Fin k → E, ∑ i, a i ∂Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) = 0 := by
  have hi (i : Fin k) : Integrable (fun a : Fin k → E => a i)
      (Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) :=
    (gaussianAmbientRows_coordinate_memLp i).integrable (by norm_num)
  rw [integral_finset_sum _ (fun i _ => hi i)]
  have he (i : Fin k) : (∫ a : Fin k → E, a i ∂Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) = 0 := by
    have hm := integral_map_of_stronglyMeasurable
      (μ := Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E))
      (measurable_pi_apply i) (stronglyMeasurable_id : StronglyMeasurable (fun a : E => a))
    rw [(finite_product_coordinate (gaussianAmbientRowLaw E) i).map_eq] at hm
    simp only [id_eq] at hm
    rw [gaussianAmbientRowLaw_mean_zero] at hm
    exact hm.symm
  simp_rw [he]
  simp

theorem gaussianSupportPosterior_aggregate_mean (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    let Q := Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)
    Q[fun a => ∑ i, a i | supportTranscriptInformation p ω n] =ᵐ[Q]
      fun a => ∫ b, ∑ i, b i ∂supportPosteriorKernel Q p ω n (supportAugmentedTranscript p a ω n) :=
  supportPosteriorKernel_aggregate_mean _ p hp ω n gaussianAmbientRows_aggregate_integrable

theorem gaussianSupportPosterior_initial_mean (p : Policy Ω S E) (ω : Ω) :
    let Q := Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)
    Q[fun a => ∑ i, a i | supportTranscriptInformation p ω 0] = fun _ => (0 : E) := by
  dsimp only
  rw [supportTranscriptInformation_zero, condExp_bot, gaussianAmbientRows_aggregate_mean_zero]

end
end Nonsmooth
