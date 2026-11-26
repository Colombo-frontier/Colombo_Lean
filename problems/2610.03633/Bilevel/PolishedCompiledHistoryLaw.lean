import Bilevel.PolishedCompiledHistory

/-! Exact stopped output law follows from the operational continuation
potential for every measurable indicator, together with unit total mass. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedCompiledHistory
open OracleCode Stateful HistoryProgram PolishedHistory
set_option autoImplicit false
variable {Q O A B H : Space}

private theorem probability_eq_of_le {Z : Type*} [MeasurableSpace Z]
    (μ ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hle : μ≤ν) : μ=ν := by
  apply Measure.ext
  intro s hs
  apply le_antisymm (hle s)
  apply (ENNReal.toReal_le_toReal (measure_ne_top ν s) (measure_ne_top μ s)).mp
  have hμ : (μ s).toReal+(μ sᶜ).toReal=1 := by
    rw [←ENNReal.toReal_add (measure_ne_top μ s) (measure_ne_top μ sᶜ),
      measure_add_measure_compl hs,measure_univ]
    norm_num
  have hν : (ν s).toReal+(ν sᶜ).toReal=1 := by
    rw [←ENNReal.toReal_add (measure_ne_top ν s) (measure_ne_top ν sᶜ),
      measure_add_measure_compl hs,measure_univ]
    norm_num
  have hc := ENNReal.toReal_mono (measure_ne_top ν sᶜ) (hle sᶜ)
  linarith

namespace Summary
variable {m : Machine Q O A B} {c : Code Q O A B} {R : HistoryProgram.Oracle Q O H}
  (T : Summary m c R)

include T in
/-- Exact law of the actual first-halt output under an arbitrary response
kernel, for every public input and every initial hidden history. -/
theorem stopped_output_law (a : A) (h₀ : H)
    (hcost : (∫⁻ y,(y.2.2:ℝ≥0∞)
      ∂(OracleCode.History.denote R.law R.update R.update_measurable c).law (a,h₀))≠⊤) :
    (trajectoryLaw m.program R (Measure.dirac a) m.start h₀).map
      (HistoryProgram.stoppedOutput m.program)=
    ((OracleCode.History.denote R.law R.update R.update_measurable c).law (a,h₀)).map Prod.fst := by
  let D := OracleCode.History.denote R.law R.update R.update_measurable c
  let μ := (trajectoryLaw m.program R (Measure.dirac a) m.start h₀).map
    (HistoryProgram.stoppedOutput m.program)
  let ν := (D.law (a,h₀)).map Prod.fst
  haveI : IsProbabilityMeasure (trajectoryLaw m.program R (Measure.dirac a) m.start h₀) :=
    trajectoryLaw_probability m.program R _ m.start m.start_measurable h₀
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_map
    (HistoryProgram.stoppedOutput_measurable m.program).aemeasurable
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_map measurable_fst.aemeasurable
  change μ=ν
  apply probability_eq_of_le μ ν
  apply Measure.le_iff.mpr
  intro s hs
  let loss : B → ℝ := s.indicator (fun _ => 1)
  have hloss : Measurable loss := measurable_const.indicator hs
  have hinner : Measurable (fun a => ∫⁻ y,(y.2.2:ℝ≥0∞) ∂D.law (a,h₀)) :=
    ((measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp
      (measurable_snd.comp measurable_snd)).lintegral_kernel.comp
        (measurable_id.prodMk measurable_const)
  have hc : (∫⁻ a,∫⁻ y,(y.2.2:ℝ≥0∞) ∂D.law (a,h₀) ∂Measure.dirac a)≠⊤ := by
    rwa [lintegral_dirac' a hinner]
  have hb := T.stopped_loss_le_denote (Measure.dirac a) h₀ hc loss hloss
  have htest : Measurable (fun y : Outcome B H => ENNReal.ofReal (loss y.1)) :=
    (hloss.comp measurable_fst).ennreal_ofReal
  have hmeas : Measurable (fun a => ∫⁻ y,ENNReal.ofReal (loss y.1) ∂D.law (a,h₀)) :=
    htest.lintegral_kernel.comp (measurable_id.prodMk measurable_const)
  change (∫⁻ w,ENNReal.ofReal (loss (HistoryProgram.stoppedOutput m.program w))
      ∂trajectoryLaw m.program R (Measure.dirac a) m.start h₀)≤
    (∫⁻ a,∫⁻ y,ENNReal.ofReal (loss y.1) ∂D.law (a,h₀) ∂Measure.dirac a) at hb
  rw [lintegral_dirac' a hmeas] at hb
  have he : ∀ b,ENNReal.ofReal (loss b)=s.indicator (fun _ => (1:ℝ≥0∞)) b := by
    intro b
    by_cases hb : b∈s <;> simp [loss,Set.indicator_of_mem,Set.indicator_of_not_mem,hb]
  simp_rw [he] at hb
  have hl : (∫⁻ w,s.indicator (fun _ => (1:ℝ≥0∞)) (HistoryProgram.stoppedOutput m.program w)
      ∂trajectoryLaw m.program R (Measure.dirac a) m.start h₀)=μ s := by
    rw [←lintegral_map (measurable_const.indicator hs)
      (HistoryProgram.stoppedOutput_measurable m.program)]
    exact lintegral_indicator_one hs
  have hr : (∫⁻ y,s.indicator (fun _ => (1:ℝ≥0∞)) y.1 ∂D.law (a,h₀))=ν s := by
    rw [←lintegral_map (measurable_const.indicator hs) measurable_fst]
    exact lintegral_indicator_one hs
  rwa [hl,hr] at hb

end Summary

/-- The compiled syntax realizes its history-kernel output denotation at
the actual stopping time; finite denotation cost ensures termination. -/
theorem compiled_stopped_output_law (R : HistoryProgram.Oracle Q O H) (q₀ : Q) (o₀ : O)
    (c : Code Q O A B) (a : A) (h₀ : H)
    (hcost : (∫⁻ y,(y.2.2:ℝ≥0∞)
      ∂(OracleCode.History.denote R.law R.update R.update_measurable c).law (a,h₀))≠⊤) :
    (trajectoryLaw (compile q₀ o₀ c).program R (Measure.dirac a) (compile q₀ o₀ c).start h₀).map
      (HistoryProgram.stoppedOutput (compile q₀ o₀ c).program)=
    ((OracleCode.History.denote R.law R.update R.update_measurable c).law (a,h₀)).map Prod.fst :=
  (compileSummary R q₀ o₀ c).stopped_output_law a h₀ hcost

end Bilevel.PolishedCompiledHistory
