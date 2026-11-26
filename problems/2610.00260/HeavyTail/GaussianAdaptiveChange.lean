import HeavyTail.GaussianTranslation
import HeavyTail.GaussianLowerPredictable

/-! Change of measure for a fresh Gaussian increment whose shift is selected
measurably from an arbitrary past state. Both measures are actual pushforwards
or densities; the change-of-law identity is proved from Gaussian translation. -/

open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace HeavyTail.GaussianLower
noncomputable section

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [MeasurableSpace Ω]

def conditionalGaussianShift (d : Ω → E) (ω : Ω × E) : Ω × E :=
  (ω.1, d ω.1 + ω.2)

lemma conditionalGaussianShift_measurable {d : Ω → E} (hd : Measurable d) :
    Measurable (conditionalGaussianShift d) := by
  unfold conditionalGaussianShift
  fun_prop

theorem conditionalGaussian_translation (P : Measure Ω) {d : Ω → E} (hd : Measurable d) :
    (P.prod (GaussianEstimates.euclideanGaussianLaw E)).withDensity
      (fun ω ↦ ENNReal.ofReal (exponentialRatio (d ω.1) ω.2)) =
      (P.prod (GaussianEstimates.euclideanGaussianLaw E)).map (conditionalGaussianShift d) := by
  have hr : Measurable (fun ω : Ω × E ↦ ENNReal.ofReal (exponentialRatio (d ω.1) ω.2)) := by
    unfold exponentialRatio
    fun_prop
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  rw [lintegral_withDensity_eq_lintegral_mul _ hr hf,
    lintegral_map hf (conditionalGaussianShift_measurable hd)]
  simp only [Pi.mul_apply]
  have hfshift : Measurable (fun ω : Ω × E ↦ f (conditionalGaussianShift d ω)) :=
    hf.comp (conditionalGaussianShift_measurable hd)
  rw [lintegral_prod _ (hr.mul hf).aemeasurable,
    lintegral_prod _ hfshift.aemeasurable]
  apply lintegral_congr
  intro ω
  have hfw : Measurable (fun z : E ↦ f (ω, z)) := hf.comp measurable_prodMk_left
  have hlocal := congrArg (fun Q : Measure E ↦ ∫⁻ z, f (ω, z) ∂Q)
    (euclideanGaussian_translation E (d ω))
  dsimp only at hlocal
  rw [lintegral_withDensity_eq_lintegral_mul _ (by unfold exponentialRatio; fun_prop) hfw,
    lintegral_map hfw (by fun_prop)] at hlocal
  exact hlocal

theorem weighted_conditionalGaussian_translation (P : Measure Ω)
    {W : Ω → ℝ} {d : Ω → E} (hW : Measurable W) (hd : Measurable d)
    (hW0 : ∀ ω, 0 ≤ W ω) :
    ((P.withDensity (fun ω ↦ ENNReal.ofReal (W ω))).prod
      (GaussianEstimates.euclideanGaussianLaw E)).map (conditionalGaussianShift d) =
      (P.prod (GaussianEstimates.euclideanGaussianLaw E)).withDensity
        (fun ω ↦ ENNReal.ofReal (likelihoodStep W d ω)) := by
  rw [← conditionalGaussian_translation _ hd,
    prod_withDensity_left hW.ennreal_ofReal]
  have hwf : Measurable (fun ω : Ω × E ↦ ENNReal.ofReal (W ω.1)) := by fun_prop
  have hrf : Measurable (fun ω : Ω × E ↦ ENNReal.ofReal (exponentialRatio (d ω.1) ω.2)) := by
    unfold exponentialRatio
    fun_prop
  rw [← withDensity_mul _ hwf hrf]
  congr 1
  funext ω
  exact (ENNReal.ofReal_mul (hW0 ω.1)).symm

/-- A local transition identity transfers an actual old likelihood to the new state law. -/
theorem gaussian_transition_change_of_measure {Ξ : Type*} [MeasurableSpace Ξ]
    (P Q : Measure Ω) {W : Ω → ℝ} {d : Ω → E}
    (hW : Measurable W) (hd : Measurable d) (hW0 : ∀ ω, 0 ≤ W ω)
    (hPQ : P = Q.withDensity (fun ω ↦ ENNReal.ofReal (W ω)))
    {Φ Ψ : Ω × E → Ξ} {R : Ξ → ℝ} (hΦ : Measurable Φ) (hR : Measurable R)
    (hshift : Ψ = Φ ∘ conditionalGaussianShift d)
    (hRstep : ∀ ω, R (Φ ω) = likelihoodStep W d ω) :
    (P.prod (GaussianEstimates.euclideanGaussianLaw E)).map Ψ =
      ((Q.prod (GaussianEstimates.euclideanGaussianLaw E)).map Φ).withDensity
        (fun y ↦ ENNReal.ofReal (R y)) := by
  rw [hPQ, hshift, ← Measure.map_map hΦ (conditionalGaussianShift_measurable hd),
    weighted_conditionalGaussian_translation Q hW hd hW0]
  have he : (fun ω ↦ ENNReal.ofReal (likelihoodStep W d ω)) =
      (fun y ↦ ENNReal.ofReal (R y)) ∘ Φ := by
    funext ω
    rw [Function.comp_apply, hRstep]
  rw [he, map_withDensity_comp _ hΦ hR.ennreal_ofReal]

end
end HeavyTail.GaussianLower
