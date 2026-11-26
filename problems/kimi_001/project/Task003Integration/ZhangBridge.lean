import Task003Integration.ZhangHardness
import Nonsmooth.CompleteGaussianHardness

noncomputable section
set_option autoImplicit false
namespace Task003Integration

theorem zhang_fixed_prior_hardness :
    Task003.ZhangInterface.ZhangPrinciple 256 (1/512) (7/512) (1/(65536*513)) := by
  apply zhang_fixed_prior_hardness_of_adaptive
  intro d _instD
  change Nonsmooth.GaussianAdaptiveHardnessInput (ZhangPoint d) (1/(65536*513))
  have hcp : Nonsmooth.posteriorSupportProbabilityConstant 512 = (1/(65536*513):ℝ) := by
    norm_num [Nonsmooth.posteriorSupportProbabilityConstant]
  rw [← hcp]
  exact Nonsmooth.gaussianAdaptiveHardness_proved

theorem zhangLiteratureInput_proved : Task003.LiteratureMain.ZhangLiteratureInput := by
  refine ⟨256,1/512,7/512,1/(65536*513),by norm_num,by norm_num,by norm_num,
    by norm_num,by norm_num,by norm_num,zhang_fixed_prior_hardness⟩

end Task003Integration
