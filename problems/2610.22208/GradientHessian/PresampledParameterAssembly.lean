import GradientHessian.PresampledLowerParameters
import GradientHessian.ParameterOptimization

/-! The actual construction-to-model implication, with all absolute
parameter choices, dimension rounding, padding and virtual-output loss.
Only the literal early expectation remains to be supplied. -/

noncomputable section
namespace GradientHessian.PresampledConstruction
open MeasureTheory HigherHierarchy RepairAllocation

def lowerGapConstant : ℝ := normalizedGapConstant lowerK
def lowerDimensionConstant : ℝ := PhysicalDimension.finalCoefficient lowerCp
  ((lowerKappa:ℝ)*(lowerRankConstant+1))

theorem lowerGapConstant_pos : 0<lowerGapConstant :=
  normalizedGapConstant_pos (by norm_num [lowerK])

theorem lowerDimensionConstant_pos : 0<lowerDimensionConstant :=
  PhysicalDimension.finalCoefficient_pos _ _

theorem lowerRateConstant_pos : 0<lowerRateConstant :=
  div_pos ForkLifetime.lifetimeFraction_pos (by norm_num)

theorem lowerSettings_dimension (J : ℕ) (hJ : ForkLifetime.depthThreshold≤J) (t : ℕ) :
    (PhysicalDimension.count lowerCp (lowerSettings J hJ).D (lowerSettings J hJ).M (t+1):ℝ)≤
      lowerDimensionConstant*((1+4096*(J:ℝ)^2)^(3/2:ℝ)+Real.log (2+(8:ℝ)^(t+1))) := by
  have hd := ofScale_dimension (Cp := lowerCp) (KA := lowerRankConstant)
    (by norm_num [lowerCp,lowAllocation]) lowerRankConstant_ge_one J lowerKappa
    (lower_J_ge_four hJ) (by norm_num [lowerKappa]) t
  rw [source_allocation] at hd
  exact hd

theorem uniform_parameter_of_early
    (hearly : ∀ (J : ℕ) (hJ : ForkLifetime.depthThreshold≤J) (t : ℕ),
      NormalizedEarlyBound lowerCp lowerK (lowerSettings J hJ) t (ForkLifetime.lifetime J)) :
    Model.UniformParameterLowerBound := by
  refine ⟨lowerGapConstant,lowerDimensionConstant,lowerRateConstant,ForkLifetime.depthThreshold,
    lowerGapConstant_pos,lowerDimensionConstant_pos,lowerRateConstant_pos,ForkLifetime.depthThreshold_pos,?_⟩
  intro J L d H T hJ hL
  cases L with
  | zero => omega
  | succ t =>
    dsimp only
    intro hT hd hH
    let s := lowerSettings J hJ
    have hm : (s.M:ℝ)=1+4096*(J:ℝ)^2 := by
      simp [s,lowerSettings,Settings.ofScale,Settings.M]; ring
    have hdim : PhysicalDimension.count lowerCp s.D s.M (t+1)≤d := by
      have hh := lowerSettings_dimension J hJ t
      exact_mod_cast hh.trans hd
    have hell : 0<ForkLifetime.lifetime J := by
      have hp := ForkLifetime.source_parameters (M := s.M) (r := s.r)
        (by simp [s,lowerSettings,Settings.ofScale,Settings.M]) hJ (lowerSettings_rank J hJ).1
      omega
    have hellM : ForkLifetime.lifetime J≤s.M := lifetime_le_marked J
    have hgap : normalizedGapConstant lowerK*8^(t+1)*s.M≤T := by
      rw [hm]
      exact hT
    have hc := complexity_of_early (Cp := lowerCp) (K := lowerK) (T := T)
      s t (ForkLifetime.lifetime J) H (by norm_num [lowerK]) le_rfl
      (lowerSettings_rank J hJ).2 hell hellM hH hgap (hearly J hJ t)
    have hr := lower_rate_le_slots hJ (n := (8:ℝ)^(t+1)) (by positivity)
    rw [hm] at hc
    exact (ENNReal.ofReal_le_ofReal hr).trans
      (hc.trans (Model.complexity_mono_dimension hdim H T))

theorem main_lower_of_early
    (hearly : ∀ (J : ℕ) (hJ : ForkLifetime.depthThreshold≤J) (t : ℕ),
      NormalizedEarlyBound lowerCp lowerK (lowerSettings J hJ) t (ForkLifetime.lifetime J)) :
    Model.MainLowerBound :=
  Model.uniformParameterLowerBound_implies_mainLowerBound (uniform_parameter_of_early hearly)

end GradientHessian.PresampledConstruction
