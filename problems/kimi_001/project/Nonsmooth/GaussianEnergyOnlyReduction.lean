import Nonsmooth.AllStepGaussianCovariance
import Nonsmooth.GaussianRowCovarianceHardness

open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- The logarithmic mean-increment proposition, proved with constant 512 in
AllStepGaussianEnergy. Covariance and directional residual estimates are proved separately. -/
def GaussianPosteriorLogEnergyEstimate (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] (C : ℝ) : Prop :=
  ∀ (k : ℕ) (hk : 0 < k),
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    4096 ≤ Module.finrank ℝ E → (k : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 512 →
    ∀ (S : Type) (mS : MeasurableSpace S), letI := mS
      ∀ p : Policy Unit S E, p.IsMeasurable →
        ∀ n : ℕ, (∫ a, ‖gaussianSupportMean p () (n + 1) a - gaussianSupportMean p () n a‖ ^ 2
          ∂Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) ≤
            C * Real.log (Real.exp 1 * k) / (Module.finrank ℝ E : ℝ)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianPosteriorRowEstimates_of_log_energy {C : ℝ}
    (hEnergy : GaussianPosteriorLogEnergyEstimate E C) : GaussianPosteriorRowEstimates E C := by
  intro k hk
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  dsimp only
  intro hd hkd S mS
  letI : MeasurableSpace S := mS
  intro p hp
  exact ⟨hEnergy k hk hd hkd S mS p hp,
    fun n => gaussianSupportPosterior_all_step_covariance p hp () n⟩

theorem supportHardnessInput_of_log_energy {C : ℝ} (hC : 0 ≤ C)
    (hEnergy : GaussianPosteriorLogEnergyEstimate E C) :
    SupportHardnessInput E (1 / 512) (posteriorSupportProbabilityConstant C) (1 / 4) 256 :=
  supportHardnessInput_of_row_estimates hC (gaussianPosteriorRowEstimates_of_log_energy hEnergy)

end
end Nonsmooth
