import Nonsmooth.GaussianRowCovarianceResidual
import Nonsmooth.GaussianPosteriorHardness

open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- Logarithmic mean increments and covariance estimates for the actual posterior rows.
CompleteGaussianHardness proves this proposition with constant 512. -/
def GaussianPosteriorRowEstimates (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] (C : ℝ) : Prop :=
  ∀ (k : ℕ) (hk : 0 < k),
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    4096 ≤ Module.finrank ℝ E → (k : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 512 →
    ∀ (S : Type) (mS : MeasurableSpace S), letI := mS
      ∀ p : Policy Unit S E, p.IsMeasurable →
        let Q := Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)
        (∀ n : ℕ, (∫ a, ‖gaussianSupportMean p () (n + 1) a - gaussianSupportMean p () n a‖ ^ 2 ∂Q) ≤
          C * Real.log (Real.exp 1 * k) / (Module.finrank ℝ E : ℝ)) ∧
        (∀ n : ℕ, ∀ᵐ h ∂Q.map (fun a => supportAugmentedTranscript p a () n), ∀ (u : E) (i : Fin k),
          variance (fun a : Fin k → E => ⟪u, a i⟫_ℝ) (supportPosteriorKernel Q p () n h) ≤
            ‖u‖ ^ 2 / (Module.finrank ℝ E : ℝ))

theorem gaussianPosteriorEstimates_of_row_estimates {C : ℝ} (hrow : GaussianPosteriorRowEstimates E C) :
    GaussianPosteriorEstimates E C := by
  intro k hk
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  dsimp only
  intro hd hkd S mS
  letI : MeasurableSpace S := mS
  intro p hp
  have h := hrow k hk hd hkd S mS p hp
  refine ⟨h.1, ?_⟩
  intro n X hX hXb
  exact gaussianSupportMean_known_direction_residual_of_row_covariance p hp () n X hX hXb (h.2 n)

theorem supportHardnessInput_of_row_estimates {C : ℝ} (hC : 0 ≤ C)
    (hrow : GaussianPosteriorRowEstimates E C) :
    SupportHardnessInput E (1 / 512) (posteriorSupportProbabilityConstant C) (1 / 4) 256 :=
  supportHardnessInput_of_posterior_estimates hC (gaussianPosteriorEstimates_of_row_estimates hrow)

end
end Nonsmooth
