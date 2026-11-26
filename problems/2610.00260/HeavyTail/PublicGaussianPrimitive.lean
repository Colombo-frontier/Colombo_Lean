import HeavyTail.GaussianPrimitive
import HeavyTail.GaussianCenteredStagePolicy
import HeavyTail.MixtureFiniteNet

/-! A single public measurable stage policy, chosen before the private
instance, works at every feasible center within the certified radius.
The finite offset net is chosen once at zero and translated by the seed. -/
noncomputable section
open MeasureTheory Set
open scoped Classical

namespace HeavyTail.PublicProblem
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {θ : OracleParameters}

theorem public_gaussian_primitive (B : PublicProblem E θ) {R τ α : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (hα : 0 < α) (hα1 : α < 1 / 10) (hnlog : confidenceLog α ≤ (n : ℝ)) :
    ∃ A : AdaptiveKernel.Policy B.X B.X E B.X (4 * n),
      ∀ I : PrivateInstance B, ∀ c : B.X, ‖(c : E) - I.minimizer‖ ≤ R →
        (A.outputLaw (Measure.dirac c) I.oracle).real
          {x | ENNReal.ofReal (acceptedStageConstant θ.p * R *
            fixedThresholdAmplitude θ.G θ.L θ.s θ.p α τ n) < I.loss x} ≤ α := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hρ : 0 < R / (8 * (n : ℝ)) := by positivity
  obtain ⟨Z, hZ, hzero, hball, hcover⟩ := finite_ball_comparator_net (0 : E) hR.le hρ
  letI : Fintype Z := hZ.fintype
  letI : Nonempty Z := ⟨⟨0, hzero⟩⟩
  letI : DecidableEq Z := fun x y => Classical.propDecidable (x = y)
  let offsets : Z → E := Subtype.val
  let i₀ : Z := ⟨0, hzero⟩
  have hb : ∀ i : Z, ‖offsets i‖ ≤ R := by
    intro i
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hball i.property
  have hz : offsets i₀ = 0 := rfl
  have hcov : ∀ u : E, ‖u‖ ≤ R → ∃ i : Z, ‖offsets i - u‖ ≤ R / (8 * n) := by
    intro u hu
    obtain ⟨z, hz, hnear⟩ := hcover u (by simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hu)
    refine ⟨⟨z, hz⟩, ?_⟩
    simpa only [offsets, norm_sub_rev] using hnear.le
  have hp := gaussianStage_parameters hτ hR hn hα hα1
  let C : GaussianStageConfig Z E R := {
    a := gaussianStageSmoothing R α
    eta := gaussianStageStep θ τ R α n
    beta := gaussianStageQuadratic θ τ R α n
    epsilon := gaussianStageResidual θ τ R α n
    epsilon_pos := hp.2.2.2.2.2
    offsets := offsets
    offsets_bound := hb
    initial := ⟨Pi.single i₀ 1, single_mem_stdSimplex ℝ i₀⟩ }
  refine ⟨B.gaussianCenteredStagePolicy hR hn τ C (4 * n), ?_⟩
  intro I c hc
  rw [B.gaussianCenteredStagePolicy_outputLaw_dirac hR hn τ C c (4 * n) I.oracle]
  simpa only [GaussianStageConfig.learner, C] using
    I.translatedGaussianPrimitive_loss hR hn hτ offsets hb i₀ hz hcov hc
      (Measure.dirac PUnit.unit) hα hα1 hnlog

end HeavyTail.PublicProblem
