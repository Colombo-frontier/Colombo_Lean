import SphereSmoothingHaarGradient
import HaarRebalancingModel
open MeasureTheory MeasureTheory.Measure Set Metric Function Filter
open Task006.HaarRebalancing Task006.SphereSmoothing
open scoped NNReal Topology
namespace Task006.Full.SampleInstance
variable {d : ℕ} {L R : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] (I : SampleInstance d L R Ω μ)

/-- The source's samplewise-before-expectation gradient identity, stated on
one common full-measure sample set and every legal inner neighborhood. -/
theorem ballSmooth_samplewise_hasGradient_haar (hR : 0 ≤ R) (hd : 0 < d)
    {ρ : ℝ} (hρ : 0 < ρ) (j : Fin d) :
    ∀ᵐ ω ∂μ, ∀ x : Space d, ‖x‖+ρ < 2*R →
      HasGradientAt (ballSmooth (fun y => I.sample y ω) ρ)
        (((d:ℝ)/ρ) • ∫ Q : OrthogonalGroup d,
          I.sample (x+ρ • column Q j) ω • column Q j ∂orthogonalHaarProbability d) x := by
  filter_upwards [(I.jointLipschitzSample_spec hR).2.2] with ω hsame
  intro x hx
  let F : Space d → ℝ := I.jointLipschitzSample hR ω
  have hF := (I.jointLipschitzSample_spec hR).2.1 ω
  have hlegal (y u : Space d) (hy : ‖y‖+ρ < 2*R) (hu : ‖u‖ ≤ 1) :
      y+ρ • u ∈ queryDomain d R := by
    have hn := norm_add_le y (ρ • u)
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hρ] at hn
    change dist (y+ρ • u) 0 ≤ 2*R
    rw [dist_zero_right]
    nlinarith [mul_le_mul_of_nonneg_left hu hρ.le]
  have heq : ballSmooth (fun y => I.sample y ω) ρ =ᶠ[𝓝 x] ballSmooth F ρ := by
    have hmem : {y : Space d | ‖y‖+ρ < 2*R} ∈ 𝓝 x :=
      (isOpen_lt (continuous_norm.add continuous_const) continuous_const).mem_nhds hx
    filter_upwards [hmem] with y hy
    apply integral_congr_ae
    filter_upwards [unitBallLaw_norm_le d] with u hu
    exact (hsame _ (hlegal y u hy hu)).symm
  have hmean :
      (∫ Q : OrthogonalGroup d, F (x+ρ • column Q j) • column Q j ∂orthogonalHaarProbability d) =
      (∫ Q : OrthogonalGroup d, I.sample (x+ρ • column Q j) ω • column Q j ∂orthogonalHaarProbability d) := by
    apply integral_congr_ae
    apply ae_of_all
    intro Q
    dsimp only
    rw [show F (x+ρ • column Q j)=I.sample (x+ρ • column Q j) ω from
      hsame _ (hlegal x (column Q j) hx ((orthonormal_column Q).norm_eq_one j).le)]
  have hg := ballSmooth_hasGradientAt_global hF hρ x
  rw [ballSmoothGradient_eq_haar hd hF hρ x j,hmean] at hg
  exact hg.congr_of_eventuallyEq heq

end Task006.Full.SampleInstance
