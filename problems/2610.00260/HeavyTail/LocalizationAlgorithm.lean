import HeavyTail.PublicGaussianPrimitive
import HeavyTail.LocalizationPhases
import HeavyTail.LocalizationComposition

/-! Actual public localized policies. The phase policies are chosen before
the private instance, composed using their actual output kernels, and then
padded to the prescribed raw-call horizon. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace HeavyTail
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {θ : OracleParameters}

namespace PublicProblem

theorem public_localization_phases (B : PublicProblem E θ)
    (hμ : 0 < θ.μ) (hT : 0 < θ.T) {τ R₀ : ℝ}
    (hτ : 64 * (4 * θ.G + θ.L) ≤ τ) (hR₀ : 0 < R₀)
    (hwarm : R₀ ≤ Real.sqrt 2 * θ.G / θ.μ)
    (c₀ : B.X) (hc₀ : ∀ I : PrivateInstance B, ‖(c₀ : E) - I.minimizer‖ ≤ R₀)
    {J : ℕ} (hJ : 1 ≤ J)
    (hterminal : localizationTerminalMultiplier (1 - 1 / θ.p)
      (localizationBudgetConstant (1 - 1 / θ.p) (acceptedStageConstant θ.p)) *
      fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ τ θ.T ≤
        θ.μ * finalLocalizationRadius R₀ J)
    (hbudget : localizationForwardRawBudget θ.G (θ.L ^ θ.p * τ ^ (2 - θ.p))
      θ.s θ.μ R₀ (1 - 1 / θ.p) θ.δ (acceptedStageConstant θ.p) J ≤ θ.T) :
    ∃ A : PublicPolicy B, ∀ I : PrivateInstance B,
      (PublicPolicy.outputLaw A I).real
        {x | ENNReal.ofReal (θ.μ / 2 * (finalLocalizationRadius R₀ J) ^ 2) < I.loss x} ≤ θ.δ := by
  let V := θ.L ^ θ.p * τ ^ (2 - θ.p)
  let q := 1 - 1 / θ.p
  let C₀ := acceptedStageConstant θ.p
  let R := localizationPhaseRadius R₀
  let α := localizationPhaseFailure θ.δ J
  let n := localizationForwardBudget θ.G V θ.s θ.μ R₀ q θ.δ C₀ J
  have hL : 0 < θ.L := θ.s_pos.trans_le θ.s_le_L
  have hG := θ.G_pos
  have hτpos : 0 < τ := (by positivity : 0 < 64 * (4 * θ.G + θ.L)).trans_le hτ
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hq : 0 < q := by
    have hi : 1 / θ.p < 1 := (div_lt_one (by linarith only [θ.p_gt_one] : 0 < θ.p)).mpr θ.p_gt_one
    dsimp [q]; linarith
  have hC₀ : 0 ≤ C₀ := (acceptedStageConstant_pos θ.p).le
  have hR : ∀ j, 0 < R j := localizationPhaseRadius_pos hR₀
  have hα : ∀ j, 0 < α j := localizationPhaseFailure_pos θ.δ_pos J
  have hα1 : ∀ j, α j < 1 / 10 := localizationPhaseFailure_lt_tenth θ.δ_pos.le θ.δ_lt_tenth J
  have hnlog : ∀ j, confidenceLog (α j) ≤ (n j : ℝ) :=
    localizationForwardBudget_ge_confidence θ.G_pos.le hV θ.s_pos.le hμ hR₀ hq
      θ.δ_pos θ.δ_lt_tenth hC₀ hwarm J
  have hn : ∀ j, 0 < n j := localizationForwardBudget_pos θ.G_pos.le hV θ.s_pos.le hμ hR₀ hq
      θ.δ_pos θ.δ_lt_tenth hC₀ hwarm J
  choose A hA using fun j => B.public_gaussian_primitive (hR j) (hn j) hτ (hα j) (hα1 j) (hnlog j)
  have hcost : AdaptiveKernel.stageCalls (fun j => 4 * n j) J ≤ θ.T := by
    rw [AdaptiveKernel.stageCalls_eq_sum, ← Finset.mul_sum]
    exact hbudget
  let P := (AdaptiveKernel.Policy.stages c₀ A J).pad c₀ hcost
  let Q : PublicPolicy B := {
    Seed := B.X
    seedSpace := inferInstance
    seedLaw := Measure.dirac c₀
    seed_probability := by infer_instance
    strategy := P }
  refine ⟨Q, ?_⟩
  intro I
  have hbias : ∀ j < J, θ.s * (θ.L / τ) ^ (θ.p - 1) ≤ θ.μ * R j / localizationScale C₀ := by
    intro j hj
    apply fixedThreshold_localization_bias_target θ hτpos hT hC₀
    apply hterminal.trans
    exact mul_le_mul_of_nonneg_left (localizationPhaseRadius_antitone hR₀.le hj.le) hμ.le
  have herr : ∀ j < J, C₀ * R j * fixedThresholdAmplitude θ.G θ.L θ.s θ.p (α j) τ (n j) ≤
      θ.μ / 2 * (R (j + 1)) ^ 2 := by
    intro j hj
    have hh := localizationPhaseBudget_error θ.G_pos.le hV θ.s_pos.le hμ (hR j) hq
      (localizationPhaseLog_ge_one θ.δ_pos θ.δ_lt_tenth J j) hC₀
      ((localizationPhaseRadius_le_initial hR₀.le j).trans hwarm) (hbias j hj)
    change C₀ * R j * fixedThresholdAmplitude θ.G θ.L θ.s θ.p (α j) τ (n j) ≤
      θ.μ * (R j) ^ 2 / 8 at hh
    have he : R (j + 1) = R j / 2 := localizationPhaseRadius_succ R₀ j
    rw [he]
    nlinarith only [hh]
  have hstage : ∀ j ≤ J - 1, ∀ c : B.X, ‖(c : E) - I.minimizer‖ ≤ R j →
      (A j).outputLaw (Measure.dirac c) I.oracle
        {x | ENNReal.ofReal (θ.μ / 2 * (R (j + 1)) ^ 2) < I.loss x} ≤ ENNReal.ofReal (α j) := by
    intro j hj c hc
    apply (measure_mono (fun x hx => lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (herr j (by omega))) hx)).trans
    exact measure_le_of_real_le _ _ (hA j I c hc)
  have hp := I.localized_policies_error hμ A c₀ R (fun j => (hR j).le)
    (by simpa only [R, localizationPhaseRadius_zero] using hc₀ I)
    (fun j => ENNReal.ofReal (α j)) (J - 1) hstage
  have hJeq : J - 1 + 1 = J := by omega
  rw [hJeq] at hp
  have hsum : (∑ j ∈ Finset.range J, ENNReal.ofReal (α j)) ≤ ENNReal.ofReal θ.δ := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => (hα j).le)]
    exact ENNReal.ofReal_le_ofReal (localizationPhaseFailure_sum_le θ.δ_pos.le J)
  change (((AdaptiveKernel.Policy.stages c₀ A J).pad c₀ hcost).outputLaw (Measure.dirac c₀) I.oracle).real _ ≤ _
  rw [AdaptiveKernel.Policy.pad_outputLaw]
  exact ENNReal.toReal_le_of_le_ofReal θ.δ_pos.le (hp.trans hsum)

end PublicProblem
end HeavyTail
