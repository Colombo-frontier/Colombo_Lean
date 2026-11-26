import SecondOrder.OjaAmplifiedProgram

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

abbrev BranchedOjaSeed (d : ℕ) (P : Parameters) (γ δ : ℝ) := (PUnit : Type) ⊕ OjaAmplifiedSeed d P γ δ

/-- This private seed law is fixed independently of the unknown loss and
its sample law, including the zero-dimensional and cheap-certificate cases. -/
def branchedOjaSeedLaw (P : Parameters) (d : ℕ) {γ : ℝ} (hγ : 0<γ) (δ : ℝ) :
    Measure (BranchedOjaSeed d P γ δ) :=
  if hc : zeroQueryCurvatureCase P d γ then Measure.dirac (Sum.inl PUnit.unit) else
    Measure.map Sum.inr (ojaAmplifiedSeedLaw P (not_zeroQueryCurvatureCase_dimension hc) hγ δ)

instance branchedOjaSeedLaw_probability (P : Parameters) (d : ℕ) {γ : ℝ} (hγ : 0<γ) (δ : ℝ) :
    IsProbabilityMeasure (branchedOjaSeedLaw P d hγ δ) := by
  unfold branchedOjaSeedLaw
  split
  · infer_instance
  · exact isProbabilityMeasure_map measurable_inr.aemeasurable

def branchedOjaProgram {d : ℕ} (P : Parameters) (x : Point d) (γ δ : ℝ)
    (s : BranchedOjaSeed d P γ δ) : OracleProgram (HvpQuery d) (Point d) (CurvatureReply d) :=
  if zeroQueryCurvatureCase P d γ then .done .certificate else
    s.elim (fun _ => .done .certificate) (ojaAmplifiedProgram P x γ δ)

theorem branchedOjaProgram_usesAtMost {d : ℕ} (P : Parameters) (x : Point d) (γ δ : ℝ)
    (s : BranchedOjaSeed d P γ δ) :
    OracleProgram.UsesAtMost (branchedOjaQueryCount P d γ δ) (branchedOjaProgram P x γ δ s) := by
  by_cases hc : zeroQueryCurvatureCase P d γ
  · simp only [branchedOjaQueryCount,branchedOjaProgram,if_pos hc,OracleProgram.UsesAtMost]
  · simp only [branchedOjaQueryCount,branchedOjaProgram,if_neg hc]
    cases s with
    | inl u => simp only [Sum.elim_inl,OracleProgram.UsesAtMost]
    | inr ss =>
      simp only [Sum.elim_inr]
      unfold ojaAmplifiedQueryCount ojaAmplifiedProgram
      dsimp only [OjaAmplifiedSeed] at ss
      generalize hn : ojaRepeats δ=n at ss ⊢
      have hh := ojaRepeatedProgram_usesExactly P x γ (ojaValidationFailure δ) n ss
      change OracleProgram.UsesAtMost (n*ojaTrialCallCount P d γ (ojaValidationFailure δ)) _
      exact hh.usesAtMost

theorem branchedOjaProgram_measurable {d : ℕ} (P : Parameters) (γ δ : ℝ) :
    OracleProgram.MeasurableFamily (.grad 0) .certificate
      (fun w : Point d × BranchedOjaSeed d P γ δ => branchedOjaProgram P w.1 γ δ w.2) := by
  by_cases hc : zeroQueryCurvatureCase P d γ
  · simpa only [branchedOjaProgram,if_pos hc] using
      (OracleProgram.measurableFamily_done (Y := Point d) (HvpQuery.grad (0:Point d)) (.certificate : CurvatureReply d)
        (fun _ : Point d × BranchedOjaSeed d P γ δ => .certificate) measurable_const)
  · simp only [branchedOjaProgram,if_neg hc]
    have hl := OracleProgram.measurableFamily_done (Y := Point d)
      (HvpQuery.grad (0:Point d)) (.certificate : CurvatureReply d)
      (fun _ : Point d × (PUnit : Type) => .certificate) measurable_const
    have hr := ojaAmplifiedProgram_measurable (d := d) P γ δ
    have hh := hl.prodSum hr
    exact hh

def branchedOjaProgramAlgorithm {d : ℕ} (P : Parameters) (x : Point d) (γ δ : ℝ)
    (s : BranchedOjaSeed d P γ δ) :
    OracleAlgorithm (HvpQuery d) (Point d) (CurvatureReply d) (ℕ → Point d) :=
  OracleProgram.algorithm (.grad 0) 0 .certificate (branchedOjaProgram P x γ δ s)

theorem branchedOjaProgramAlgorithm_measurable {d : ℕ} (P : Parameters) (γ δ : ℝ) :
    MeasurableOracleAlgorithmFamily (fun w : Point d × BranchedOjaSeed d P γ δ =>
      branchedOjaProgramAlgorithm P w.1 γ δ w.2) :=
  OracleProgram.algorithm_measurable 0 (branchedOjaProgram_measurable P γ δ)

end
end SecondOrder
