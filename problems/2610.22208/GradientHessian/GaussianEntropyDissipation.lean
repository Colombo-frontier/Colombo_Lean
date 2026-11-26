import GradientHessian.GaussianEntropyEnergy
import GradientHessian.GaussianFunctionalLimits
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Entropy dissipation along the actual Ornstein--Uhlenbeck semigroup.
Differentiation under the outer Gaussian integral is justified explicitly. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert Filter Set
open scoped Topology NNReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem ou_entropy_hasDerivAt {g : E → ℝ} {B C : ℝ≥0} {a b : ℝ}
    (hg : ContDiff ℝ 2 g) (hLip : LipschitzWith B g)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ (C : ℝ))
    (ha : 0 < a) (hab : ∀ x, a ≤ g x ∧ g x ≤ b) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x, ornsteinUhlenbeck E s g x * Real.log (ornsteinUhlenbeck E s g x)
      ∂euclideanGaussianLaw E)
      (-(∫ x, fisherIntegrand E (ornsteinUhlenbeck E t g) x ∂euclideanGaussianLaw E)) t := by
  have hc (s : ℝ) : ContDiff ℝ 2 (ornsteinUhlenbeck E s g) := mehler_contDiff_two hg hLip hH _
  have hbounds (s : ℝ) (x : E) :
      a ≤ ornsteinUhlenbeck E s g x ∧ ornsteinUhlenbeck E s g x ≤ b :=
    mehler_value_bounds hLip hab _ x
  have hpos (s : ℝ) (x : E) : 0 < ornsteinUhlenbeck E s g x := ha.trans_le (hbounds s x).1
  let S := 1 + |Real.log a| + |Real.log b|
  have hS : 0 ≤ S := by dsimp [S]; positivity
  let F : ℝ → E → ℝ := fun s x =>
    ornsteinUhlenbeck E s g x * Real.log (ornsteinUhlenbeck E s g x)
  let F' : ℝ → E → ℝ := fun s x => (1 + Real.log (ornsteinUhlenbeck E s g x)) *
    gaussianGenerator E (ornsteinUhlenbeck E s g) x
  let bound : E → ℝ := fun x => S * ((Module.finrank ℝ E : ℝ) * C + B * ‖x‖)
  obtain ⟨ε, hε, hlocal⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_gt_nhds ht)
  have hmeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) (euclideanGaussianLaw E) :=
    Eventually.of_forall (fun s => (Real.continuous_mul_log.comp (hc s).continuous).aestronglyMeasurable)
  have hint : Integrable (F t) (euclideanGaussianLaw E) := by
    obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
      Real.continuous_mul_log.continuousOn
    exact gaussian_bounded_integrable E (Real.continuous_mul_log.comp (hc t).continuous)
      (fun x => hK _ (hbounds t x))
  have hdmeas : AEStronglyMeasurable (F' t) (euclideanGaussianLaw E) :=
    ((continuous_const.add ((hc t).continuous.log (fun x => (hpos t x).ne'))).mul
      (gaussian_generator_continuous E (hc t))).aestronglyMeasurable
  have hbnd : ∀ᵐ x ∂euclideanGaussianLaw E, ∀ s ∈ Metric.ball t ε, ‖F' s x‖ ≤ bound x := by
    apply ae_of_all
    intro x s hs
    have hsp : 0 < s := hlocal s hs
    dsimp only [F', bound]
    rw [norm_mul]
    exact mul_le_mul (entropySlope_bound E ha (hbounds s) x)
      (gaussian_generator_norm_le E (ou_lipschitz E hg hLip hsp.le)
        (ou_hessian_bound E hg hLip hH hsp.le) x) (norm_nonneg _) hS
  have hbound : Integrable bound (euclideanGaussianLaw E) :=
    ((integrable_const _).add ((norm_integrable E).const_mul (B : ℝ))).const_mul S
  have hdiff : ∀ᵐ x ∂euclideanGaussianLaw E, ∀ s ∈ Metric.ball t ε,
      HasDerivAt (fun r => F r x) (F' s x) s := by
    apply ae_of_all
    intro x s hs
    have hd := (Real.hasDerivAt_mul_log (hpos s x).ne').comp s
      (ornsteinUhlenbeck_time_generator E hg hLip hH (hlocal s hs) x)
    simpa only [F, F', add_comm (Real.log (ornsteinUhlenbeck E s g x)) 1] using hd
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hε hmeas hint hdmeas hbnd hbound hdiff).2
  have he : (∫ x, F' t x ∂euclideanGaussianLaw E) =
      -(∫ x, fisherIntegrand E (ornsteinUhlenbeck E t g) x ∂euclideanGaussianLaw E) :=
    gaussian_entropy_generator E (hc t) (ou_lipschitz E hg hLip ht.le)
      (ou_hessian_bound E hg hLip hH ht.le) ha (hbounds t)
  exact he ▸ hd

end GradientHessian.GaussianConcentration
