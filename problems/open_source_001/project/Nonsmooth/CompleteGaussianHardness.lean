import Nonsmooth.AllStepGaussianEnergy

open MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianPosteriorRowEstimates_proved : GaussianPosteriorRowEstimates E 512 :=
  gaussianPosteriorRowEstimates_of_log_energy gaussianPosteriorLogEnergyEstimate_proved

theorem gaussianPosteriorEstimates_proved : GaussianPosteriorEstimates E 512 :=
  gaussianPosteriorEstimates_of_row_estimates gaussianPosteriorRowEstimates_proved

theorem gaussianAdaptiveHardness_proved :
    GaussianAdaptiveHardnessInput E (posteriorSupportProbabilityConstant 512) :=
  gaussian_adaptive_hardness_of_posterior_estimates (by norm_num) gaussianPosteriorEstimates_proved

theorem supportHardnessInput_proved :
    SupportHardnessInput E (1 / 512) (posteriorSupportProbabilityConstant 512) (1 / 4) 256 :=
  supportHardnessInput_of_log_energy (by norm_num) gaussianPosteriorLogEnergyEstimate_proved

end
end Nonsmooth
