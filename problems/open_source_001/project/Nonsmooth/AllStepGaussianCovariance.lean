import Nonsmooth.GaussianPolytopeCovariance
import Nonsmooth.GaussianBaseCovarianceReduction
import Nonsmooth.GaussianRowCovarianceResidual

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianPolytopeModel_covariance (s : ℝ) (M : GaussianPolytopeModel E) (v : E) :
    variance (fun z : E => ⟪v, z⟫_ℝ) (gaussianPolytopeModelLaw s M) ≤ s ^ 2 * ‖v‖ ^ 2 :=
  gaussianPolytopeModel_covariance_of_base s M
    (gaussianBallPolytope_covariance M.radius_nonneg M.normal M.bound M.positive) v

/-- Every finite adaptive history has the sharp row covariance bound
for the manuscript's actual Gaussian posterior kernel. -/
theorem gaussianSupportPosterior_all_step_covariance {k : ℕ} [Nonempty (Fin k)]
    {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    let Q := Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)
    ∀ᵐ h ∂Q.map (fun a => supportAugmentedTranscript p a ω n), ∀ (v : E) (i : Fin k),
      variance (fun a : Fin k → E => ⟪v, a i⟫_ℝ) (supportPosteriorKernel Q p ω n h) ≤
        ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  cases k with
  | zero => exact Fin.elim0 (Classical.choice (inferInstance : Nonempty (Fin 0)))
  | succ r =>
    exact gaussianSupportPosterior_covariance_of_base_models
      (fun M v => gaussianBallPolytope_covariance M.radius_nonneg M.normal M.bound M.positive v)
      p hp ω n

/-- The sharp residual estimate holds even when the tested direction
is selected measurably from the entire current adaptive history. -/
theorem gaussianSupportMean_all_step_directional_residual {k : ℕ} [Nonempty (Fin k)]
    {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ)
    (X : (Fin k → E) → E)
    (hX : AEStronglyMeasurable[supportTranscriptInformation p ω n] X
      (Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)))
    (hXb : ∀ a, ‖X a‖ ≤ 1) :
    (∫ a : Fin k → E, ⟪(∑ i, a i) - gaussianSupportMean p ω n a, X a⟫_ℝ ^ 2
      ∂Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) ≤
      (k : ℝ) / (Module.finrank ℝ E : ℝ) :=
  gaussianSupportMean_known_direction_residual_of_row_covariance p hp ω n X hX hXb
    (gaussianSupportPosterior_all_step_covariance p hp ω n)

end
end Nonsmooth
