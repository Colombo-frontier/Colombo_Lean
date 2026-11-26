import HeavyTail.PublicGaussianPrimitive
import HeavyTail.BudgetRounding
import HeavyTail.AdaptiveKernelPadding
import HeavyTail.ModelQuantile

/-! The single-stage public algorithm at the full raw budget. Padding preserves
its actual law; deterministic rounding is the sole constant loss. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Classical
namespace HeavyTail
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {θ : OracleParameters}

theorem fixedCallMinimax_upper_of_public_policies (ε : ℝ≥0∞)
    (h : ∀ B : PublicProblem E θ, ∃ A : PublicPolicy B, ∀ I : PrivateInstance B,
      (PublicPolicy.outputLaw A I).real {x | ε < I.loss x} ≤ θ.δ) :
    fixedCallMinimax E θ ≤ ε := by
  choose A hA using h
  exact fixedCallMinimax_upper A ε hA

theorem PublicProblem.public_stage_at_budget (B : PublicProblem E θ) {τ R : ℝ}
    (hτ : 64 * (4 * θ.G + θ.L) ≤ τ) (hR : 0 < R)
    (c : B.X) (hc : ∀ I : PrivateInstance B, ‖(c : E) - I.minimizer‖ ≤ R)
    (hbudget : 8 * confidenceLog θ.δ ≤ θ.T) :
    ∃ A : PublicPolicy B, ∀ I : PrivateInstance B,
      (PublicPolicy.outputLaw A I).real
        {x | ENNReal.ofReal (8 * acceptedStageConstant θ.p * R *
          fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ τ θ.T) < I.loss x} ≤ θ.δ := by
  have hb := accepted_round_count_bounds (confidenceLog_ge_one θ.δ_pos θ.δ_lt_tenth) hbudget
  have hL : 0 < θ.L := θ.s_pos.trans_le θ.s_le_L
  have hG := θ.G_pos
  have hτpos : 0 < τ := (by positivity : 0 < 64 * (4 * θ.G + θ.L)).trans_le hτ
  have hC : 0 < acceptedStageConstant θ.p := acceptedStageConstant_pos θ.p
  obtain ⟨A, hA⟩ := B.public_gaussian_primitive hR hb.1 hτ θ.δ_pos θ.δ_lt_tenth hb.2.2.1
  let Q : PublicPolicy B := {
    Seed := B.X
    seedSpace := inferInstance
    seedLaw := Measure.dirac c
    seed_probability := by infer_instance
    strategy := A.pad c hb.2.1 }
  refine ⟨Q, ?_⟩
  intro I
  have hamp := fixedThresholdAmplitude_accepted_rounds θ hτpos hbudget
  have herr : acceptedStageConstant θ.p * R *
      fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ τ (θ.T / 4) ≤
      8 * acceptedStageConstant θ.p * R *
      fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ τ θ.T := by
    nlinarith only [mul_le_mul_of_nonneg_left hamp (mul_nonneg hC.le hR.le)]
  change ((A.pad c hb.2.1).outputLaw (Measure.dirac c) I.oracle).real _ ≤ _
  rw [AdaptiveKernel.Policy.pad_outputLaw]
  exact (measureReal_mono (fun x hx => lt_of_le_of_lt (ENNReal.ofReal_le_ofReal herr) hx)).trans
    (hA I c (hc I))

theorem single_stage_fixedCallMinimax_upper {τ : ℝ}
    (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (hbudget : 8 * confidenceLog θ.δ ≤ θ.T) :
    fixedCallMinimax E θ ≤ ENNReal.ofReal (8 * acceptedStageConstant θ.p * θ.D *
      fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ τ θ.T) := by
  apply fixedCallMinimax_upper_of_public_policies
  intro B
  exact B.public_stage_at_budget hτ θ.D_pos ⟨B.initial, B.initial_feasible⟩
    (fun I => I.initial_distance) hbudget

end HeavyTail
