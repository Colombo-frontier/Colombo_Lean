import GradientHessian.GaussianConcentrationSmoothing
import GradientHessian.GaussianConcentrationLimits

/-! Endpoint limits for arbitrary continuous functions of a bounded
Gaussian semigroup trajectory, including the entropy integrand. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert Filter Set
open scoped Topology

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def mehlerFunctional (f : E → ℝ) (ψ : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  ∫ x, ψ (mehler E ρ f x) ∂euclideanGaussianLaw E

theorem mehlerFunctional_continuous {f : E → ℝ} {ψ : ℝ → ℝ} {D : ℝ}
    (hf : Continuous f) (hD : ∀ x, ‖f x‖ ≤ D) (hψ : Continuous ψ) :
    Continuous (mehlerFunctional E f ψ) := by
  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc (-D) D)).exists_bound_of_continuousOn
    hψ.continuousOn
  apply continuous_of_dominated (bound := fun _ => K)
  · intro ρ
    have hc : Continuous (mehler E ρ f) := vectorMehler_continuous hf hD ρ
    exact (hψ.comp hc).aestronglyMeasurable
  · intro ρ
    apply ae_of_all
    intro x
    apply hK
    exact abs_le.mp (mehler_norm_le E hD ρ x)
  · exact integrable_const _
  · apply ae_of_all
    intro x
    have hj : Continuous (fun ρ : ℝ => (ρ, x)) := continuous_id.prodMk continuous_const
    exact hψ.comp ((mehler_joint_continuous E hf hD).comp hj)

theorem ouFunctional_continuous {f : E → ℝ} {ψ : ℝ → ℝ} {D : ℝ}
    (hf : Continuous f) (hD : ∀ x, ‖f x‖ ≤ D) (hψ : Continuous ψ) :
    Continuous (fun t => ∫ x, ψ (ornsteinUhlenbeck E t f x) ∂euclideanGaussianLaw E) :=
  (mehlerFunctional_continuous E hf hD hψ).comp (Real.continuous_exp.comp continuous_neg)

theorem ouFunctional_tendsto {f : E → ℝ} {ψ : ℝ → ℝ} {D : ℝ}
    (hf : Continuous f) (hD : ∀ x, ‖f x‖ ≤ D) (hψ : Continuous ψ) :
    Tendsto (fun t => ∫ x, ψ (ornsteinUhlenbeck E t f x) ∂euclideanGaussianLaw E)
      atTop (𝓝 (ψ (∫ x, f x ∂euclideanGaussianLaw E))) := by
  have h := (mehlerFunctional_continuous E hf hD hψ).continuousAt.tendsto.comp
    Real.tendsto_exp_neg_atTop_nhds_zero
  simpa only [mehlerFunctional, mehler_zero, integral_const,
    measureReal_univ_eq_one, smul_eq_mul, one_mul] using h

end GradientHessian.GaussianConcentration
