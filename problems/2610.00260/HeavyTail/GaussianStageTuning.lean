import HeavyTail.GaussianConcreteStage
import HeavyTail.OnlineMasterTuning
import HeavyTail.LocalizationSchedule

/-! Applying the source scalar tuning to the actual stage bound. -/
noncomputable section
namespace HeavyTail

def gaussianStageStep (θ : OracleParameters) (τ R α : ℝ) (n : ℕ) : ℝ :=
  onlineStep θ.p (acceptedMeanScale θ τ) (acceptedTraceScale θ τ)
    (acceptedWeakScale θ) R (confidenceLog α) n

def gaussianStageSmoothing (R α : ℝ) : ℝ := onlineSmoothing R (confidenceLog α)

def gaussianStageQuadratic (θ : OracleParameters) (τ R α : ℝ) (n : ℕ) : ℝ :=
  onlineQuadratic (gaussianStageStep θ τ R α n) (acceptedMeanScale θ τ) R n

def gaussianStageResidual (θ : OracleParameters) (τ R α : ℝ) (n : ℕ) : ℝ :=
  onlineResidual (gaussianStageStep θ τ R α n) (acceptedMeanScale θ τ) R n

theorem gaussianStage_parameters {θ : OracleParameters} {τ R α : ℝ} {n : ℕ}
    (hτ : 64 * (4 * θ.G + θ.L) ≤ τ) (hR : 0 < R) (hn : 0 < n)
    (hα : 0 < α) (hα1 : α < 1 / 10) :
    0 < gaussianStageStep θ τ R α n ∧
    gaussianStageStep θ τ R α n * acceptedMeanScale θ τ * R ≤ 1 / 16 ∧
    0 < gaussianStageSmoothing R α ∧ gaussianStageSmoothing R α ≤ R ∧
    0 < gaussianStageQuadratic θ τ R α n ∧ 0 < gaussianStageResidual θ τ R α n := by
  have hell := confidenceLog_ge_one hα hα1
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hM := acceptedMeanScale_pos θ hτ
  have hV := (acceptedTraceScale_pos θ hτ).le
  have hs := acceptedWeakScale_pos θ
  have hη := onlineStep_pos (p := θ.p) hM hV hs hR (lt_of_lt_of_le zero_lt_one hell) hnR
  have ha := onlineSmoothing_bounds hR hell
  refine ⟨hη, onlineStep_admissible hM hR, ha.1, ha.2.1,
    onlineQuadratic_pos hη hM hR hnR, ?_⟩
  change 0 < onlineResidual _ _ _ _
  unfold onlineResidual
  positivity

theorem stage_log_confidence_comparison {α : ℝ} (hα : 0 < α) (hα1 : α < 1 / 10) :
    Real.log (1 / (α / 4)) ≤ 2 * confidenceLog α := by
  have hratio : 1 / (α / 4) ≤ (3 / α) ^ 2 := by
    have hα9 : α ≤ 9 / 4 := by linarith
    rw [div_pow]
    apply (le_div_iff₀ (sq_pos_of_pos hα)).2
    have hid : 1 / (α / 4) * α ^ 2 = 4 * α := by field_simp; ring
    rw [hid]
    nlinarith only [hα9]
  have hlog := Real.log_le_log (by positivity : 0 < 1 / (α / 4)) hratio
  simpa only [Real.log_pow, confidenceLog] using hlog

theorem gaussianStageErrorBound_le_onlineMaster {θ : OracleParameters} {τ R α : ℝ} {n : ℕ}
    (hτ : 64 * (4 * θ.G + θ.L) ≤ τ) (hR : 0 < R) (hn : 0 < n)
    (hα : 0 < α) (hα1 : α < 1 / 10) :
    gaussianStageErrorBound θ R τ (gaussianStageSmoothing R α) (gaussianStageStep θ τ R α n)
      (gaussianStageQuadratic θ τ R α n) (gaussianStageResidual θ τ R α n)
      (α / 4) (R / (8 * n)) n ≤
    onlineMaster (GaussianEstimates.mixedConstant θ.p) θ.p (acceptedMeanScale θ τ)
      (acceptedTraceScale θ τ) (acceptedWeakScale θ) R (confidenceLog α) n +
      8 * R * acceptedBiasScale θ τ + 2 * θ.G * R / n := by
  have hparams := gaussianStage_parameters hτ hR hn hα hα1
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hden := mul_pos hparams.1 hnR
  have hlog := stage_log_confidence_comparison hα hα1
  let η := gaussianStageStep θ τ R α n
  let a := gaussianStageSmoothing R α
  let β := gaussianStageQuadratic θ τ R α n
  let ε := gaussianStageResidual θ τ R α n
  have hid : onlineMaster (GaussianEstimates.mixedConstant θ.p) θ.p (acceptedMeanScale θ τ)
      (acceptedTraceScale θ τ) (acceptedWeakScale θ) R (confidenceLog α) n +
      8 * R * acceptedBiasScale θ τ + 2 * θ.G * R / n =
      (R ^ 2 / (2 * a ^ 2) + β / 2 * R ^ 2 +
        n * (η ^ 2 * (acceptedMeanScale θ τ) ^ 2 / (2 * β) + ε) +
        8 * n * acceptedOnlineExponent θ τ R a η + 4 * confidenceLog α +
        η * (4 * n) * (acceptedMeanScale θ τ * (R / (8 * n)) +
          2 * R * acceptedBiasScale θ τ + θ.G * R / (2 * n))) / (η * n) := by
    have hη0 : η ≠ 0 := hparams.1.ne'
    have ha0 : a ≠ 0 := hparams.2.2.1.ne'
    have hβ0 : β ≠ 0 := hparams.2.2.2.2.1.ne'
    change ((R ^ 2 / (2 * a ^ 2) + β * R ^ 2 / 2 +
      n * (η ^ 2 * (acceptedMeanScale θ τ) ^ 2 / (2 * β) + ε) +
      8 * n * GaussianEstimates.mixedConstant θ.p *
        (η ^ θ.p * (acceptedWeakScale θ * R) ^ θ.p + η ^ 2 * a ^ 2 *
          (acceptedTraceScale θ τ + (acceptedMeanScale θ τ) ^ 2)) +
      4 * confidenceLog α) / (η * n) + acceptedMeanScale θ τ * R / (2 * n)) +
      8 * R * acceptedBiasScale θ τ + 2 * θ.G * R / n = _
    dsimp only [acceptedOnlineExponent]
    field_simp [hη0, ha0, hβ0, hnR.ne']
    <;> ring
  rw [hid]
  unfold gaussianStageErrorBound
  apply div_le_div_of_nonneg_right _ hden.le
  change R ^ 2 / (2 * a ^ 2) + β / 2 * R ^ 2 +
    n * (η ^ 2 * (acceptedMeanScale θ τ) ^ 2 / (2 * β) + ε) +
    2 * (4 * n * acceptedOnlineExponent θ τ R a η + Real.log (1 / (α / 4))) +
    η * (4 * n) * (acceptedMeanScale θ τ * (R / (8 * n)) +
      2 * R * acceptedBiasScale θ τ + θ.G * R / (2 * n)) ≤ _
  linarith only [hlog]

end HeavyTail
