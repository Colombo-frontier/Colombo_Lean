import GradientHessian.GaussianPoincareEnergy

/-! Actual differentiation of the Gaussian second moment along the OU
semigroup, with all domination and integration-by-parts premises proved. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert Filter
open scoped Topology NNReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem ou_squareMean_hasDerivAt {f : E → ℝ} {B C : ℝ≥0} {D : ℝ}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ))
    (hD : ∀ x, ‖f x‖ ≤ D) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x, (ornsteinUhlenbeck E s f x) ^ 2 ∂euclideanGaussianLaw E)
      (-2 * ∫ x, ‖fderiv ℝ (ornsteinUhlenbeck E t f) x‖ ^ 2 ∂euclideanGaussianLaw E) t := by
  have hDn : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  have hc (s : ℝ) : ContDiff ℝ 2 (ornsteinUhlenbeck E s f) := mehler_contDiff_two hf hLip hH _
  let F : ℝ → E → ℝ := fun s x => (ornsteinUhlenbeck E s f x) ^ 2
  let F' : ℝ → E → ℝ := fun s x => 2 * ornsteinUhlenbeck E s f x *
    gaussianGenerator E (ornsteinUhlenbeck E s f) x
  let bound : E → ℝ := fun x => 2 * D * ((Module.finrank ℝ E : ℝ) * C + B * ‖x‖)
  obtain ⟨ε, hε, hlocal⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_gt_nhds ht)
  have hmeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) (euclideanGaussianLaw E) :=
    Eventually.of_forall (fun s => ((hc s).continuous.pow 2).aestronglyMeasurable)
  have hint : Integrable (F t) (euclideanGaussianLaw E) := by
    apply gaussian_bounded_integrable E ((hc t).continuous.pow 2)
    intro x
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (mehler_norm_le E hD _ x) 2
  have hdmeas : AEStronglyMeasurable (F' t) (euclideanGaussianLaw E) :=
    ((continuous_const.mul (hc t).continuous).mul
      (gaussian_generator_continuous E (hc t))).aestronglyMeasurable
  have hbnd : ∀ᵐ x ∂euclideanGaussianLaw E, ∀ s ∈ Metric.ball t ε, ‖F' s x‖ ≤ bound x := by
    apply ae_of_all
    intro x s hs
    have hsp : 0 < s := hlocal s hs
    dsimp only [F', bound]
    rw [norm_mul, norm_mul, show ‖(2 : ℝ)‖ = 2 by norm_num]
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (mehler_norm_le E hD _ x) (by norm_num)
    · exact gaussian_generator_norm_le E (ou_lipschitz E hf hLip hsp.le)
        (ou_hessian_bound E hf hLip hH hsp.le) x
    · exact norm_nonneg _
    · positivity
  have hbound : Integrable bound (euclideanGaussianLaw E) :=
    ((integrable_const _).add ((norm_integrable E).const_mul (B : ℝ))).const_mul (2 * D)
  have hdiff : ∀ᵐ x ∂euclideanGaussianLaw E, ∀ s ∈ Metric.ball t ε,
      HasDerivAt (fun r => F r x) (F' s x) s := by
    apply ae_of_all
    intro x s hs
    simpa only [F, F', Nat.cast_ofNat, Nat.reduceSub, pow_one] using
      (ornsteinUhlenbeck_time_generator E hf hLip hH (hlocal s hs) x).pow 2
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hε hmeas hint hdmeas hbnd hbound hdiff).2
  have he : (∫ x, F' t x ∂euclideanGaussianLaw E) =
      -2 * ∫ x, ‖fderiv ℝ (ornsteinUhlenbeck E t f) x‖ ^ 2 ∂euclideanGaussianLaw E := by
    simp only [F', mul_assoc]
    rw [integral_const_mul, gaussian_dirichlet_bounded_self E (hc t)
      (ou_lipschitz E hf hLip ht.le) (ou_hessian_bound E hf hLip hH ht.le)
      (mehler_norm_le E hD _)]
    ring
  exact he ▸ hd

end GradientHessian.GaussianConcentration
