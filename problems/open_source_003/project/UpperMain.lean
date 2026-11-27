import UpperProgramRisk
import UpperProgramAccuracy

/-! A single public algorithm solves every admissible sample instance with an
explicit finite reply budget. This establishes nonemptiness before taking the
natural-number minimax infimum. The seed law is Type 0; sample spaces retain an
arbitrary universe. -/

open MeasureTheory
open Task006.UpperPublicParameters

namespace Task006.Full
universe v

noncomputable def tunedUpperAlgorithm (d : ℕ) (L R eps : ℝ) (h : Regime d L R eps) :
    OracleAlgorithm d (upperReplyCount d (tunedUpperRounds d L R eps))
      (UpperSeed d (tunedUpperRounds d L R eps)) :=
  (upperPairedProgram (tunedUpperParameters d L R eps h) (by have hd := h.1; omega)).toAlgorithm

theorem tunedUpper_solves_instance {d : ℕ} {L R eps : ℝ} (h : Regime d L R eps)
    {Ω : Type v} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (I : SampleInstance d L R Ω μ) :
    (tunedUpperAlgorithm d L R eps h).SolvesInstance eps
      (upperSeedLaw d (tunedUpperRounds d L R eps)) I := by
  let P := tunedUpperParameters d L R eps h
  have hd : 0 < d := by have hd := h.1; omega
  have hT := tunedUpperRounds_pos h
  have hR : 0 < P.R := h.2.2.1
  change (∀ seed tape, (upperPairedProgram P hd).toAlgorithm.executionLegal I.sample tape seed R) ∧
    Integrable ((upperPairedProgram P hd).toAlgorithm.realizedGap I)
      ((upperSeedLaw d (tunedUpperRounds d L R eps)).prod (iidHandleLaw μ)) ∧ _
  refine ⟨fun seed tape => upperProgram_execution_legal P hd hT I.sample tape seed,
    upperProgram_realizedGap_integrable P hd hT h.2.1.le I, ?_⟩
  have hb := I.upperProgram_risk_le P hd hT hR h.2.1 (tunedUpperParameters_rho_pos h)
    (tunedUpperParameters_clip_pos h) (tunedUpperScale_ge_one h)
  exact hb.trans (tunedUpper_accuracy h).le

theorem tunedUpper_uniformlySolves {d : ℕ} {L R eps : ℝ} (h : Regime d L R eps) :
    UniformlySolves.{0,v} L R eps (upperSeedLaw d (tunedUpperRounds d L R eps))
      (tunedUpperAlgorithm d L R eps h) := by
  intro Ω mΩ μ hμ I
  letI : IsProbabilityMeasure μ := hμ
  exact tunedUpper_solves_instance h I

/-- The admissible budget is witnessed by the actual public algorithm and its
actual Haar/ball private seed distribution, before invoking the minimax infimum. -/
theorem upper_admits_budget {d : ℕ} {L R eps : ℝ} (h : Regime d L R eps) :
    AdmitsBudget.{0,v} d (upperReplyCount d (tunedUpperRounds d L R eps)) L R eps := by
  refine ⟨UpperSeed d (tunedUpperRounds d L R eps), inferInstance,
    upperSeedLaw d (tunedUpperRounds d L R eps), inferInstance,
    tunedUpperAlgorithm d L R eps h, ?_⟩
  exact tunedUpper_uniformlySolves h

theorem upper_budget_nonempty {d : ℕ} {L R eps : ℝ} (h : Regime d L R eps) :
    {N : ℕ | AdmitsBudget.{0,v} d N L R eps}.Nonempty :=
  ⟨upperReplyCount d (tunedUpperRounds d L R eps), upper_admits_budget h⟩

theorem minimax_upper_reply_budget {d : ℕ} {L R eps : ℝ} (h : Regime d L R eps) :
    minimaxReplies.{0,v} d L R eps ≤ upperReplyCount d (tunedUpperRounds d L R eps) := by
  exact Nat.sInf_le (upper_admits_budget h)

theorem upper_reply_complexity {d : ℕ} {L R eps : ℝ} (h : Regime d L R eps) :
    (upperReplyCount d (tunedUpperRounds d L R eps) : ℝ) ≤
      (2 * publicComplexityCoefficient) * d * (L * R / eps) ^ 3 *
        Real.log (Real.exp 1 * d * (L * R / eps)) ^ (3 / 2 : ℝ) := by
  have ht := publicRounds_complexity h.1 (show 2 ≤ upperAspect L R eps by linarith [(regime_aspect h).1])
  have hm := mul_le_mul_of_nonneg_left ht (show (0 : ℝ) ≤ 2 * d by positivity)
  calc
    (upperReplyCount d (tunedUpperRounds d L R eps) : ℝ) =
        2 * (d : ℝ) * (publicRounds (upperAspect L R eps)
          (publicLogScale d (upperAspect L R eps)) : ℝ) := by
      simp only [upperReplyCount, tunedUpperRounds, tunedUpperScale, Nat.cast_mul, Nat.cast_ofNat]
    _ ≤ (2 * (d : ℝ)) * (publicComplexityCoefficient * upperAspect L R eps ^ 3 *
        Real.log (Real.exp 1 * d * upperAspect L R eps) ^ (3 / 2 : ℝ)) := hm
    _ = _ := by unfold upperAspect; ring

theorem minimax_upper_complexity {d : ℕ} {L R eps : ℝ} (h : Regime d L R eps) :
    (minimaxReplies.{0,v} d L R eps : ℝ) ≤
      (2 * publicComplexityCoefficient) * d * (L * R / eps) ^ 3 *
        Real.log (Real.exp 1 * d * (L * R / eps)) ^ (3 / 2 : ℝ) := by
  exact (Nat.cast_le.mpr (minimax_upper_reply_budget h)).trans (upper_reply_complexity h)

#print axioms tunedUpper_solves_instance
#print axioms upper_admits_budget
#print axioms minimax_upper_complexity
end Task006.Full
