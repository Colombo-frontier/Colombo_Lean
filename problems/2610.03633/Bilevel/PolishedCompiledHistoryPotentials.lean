import Bilevel.OracleCodeHistory
import Bilevel.OracleCompiler
import Bilevel.PolishedHistoryStoppedComparison

/-! Operational potential bounds for the actual history-kernel execution.
These lemmas use its first halt and extended call cost. They do not replace
execution by a compositional procedure or a stationary realization. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedCompiledHistory
open HistoryProgram PolishedHistory
set_option autoImplicit false
variable {S Q O Y H P : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y] [MeasurableSpace H] [MeasurableSpace P]
variable (A : BorelAdaptive.Program S Q O Y) (R : HistoryProgram.Oracle Q O H)
  (ρ : Measure P) (start : P → S) (hs : Measurable start) (h₀ : H)

def initialValue (V : S × H → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ p,V (start p,h₀) ∂ρ

theorem runLaw_succ (n : ℕ) :
    runLaw A R ρ start h₀ (n+1)=HistoryProgram.step A R ∘ₘ runLaw A R ρ start h₀ n := by
  rw [runLaw,run_succ,←Measure.comp_assoc]
  rfl

include hs in
theorem runLaw_initial_integral (V : S × H → ℝ≥0∞) (hV : Measurable V) :
    (∫⁻ z,V z ∂runLaw A R ρ start h₀ 0)=initialValue ρ start h₀ V := by
  rw [runLaw,run_zero,Measure.id_comp,lintegral_map hV (hs.prodMk measurable_const)]
  rfl

include hs in
theorem finite_potential_bound (V : S × H → ℝ≥0∞) (hV : Measurable V)
    (hstep : ∀ z,(∫⁻ z',V z' ∂HistoryProgram.step A R z)≤V z) (n : ℕ) :
    (∫⁻ z,V z ∂runLaw A R ρ start h₀ n)≤ initialValue ρ start h₀ V := by
  induction n with
  | zero => exact (runLaw_initial_integral A R ρ start hs h₀ V hV).le
  | succ n ih =>
      rw [runLaw_succ,Measure.lintegral_bind (Kernel.measurable _).aemeasurable hV.aemeasurable]
      exact (lintegral_mono hstep).trans ih

include hs in
theorem queryCount_integral_succ (n : ℕ) :
    (∫⁻ w,(queryCount A (n+1) w:ℝ≥0∞) ∂trajectoryLaw A R ρ start h₀)=
      (∫⁻ w,(queryCount A n w:ℝ≥0∞) ∂trajectoryLaw A R ρ start h₀)+
        ∫⁻ z,liveIndicator A z ∂runLaw A R ρ start h₀ n := by
  simp_rw [queryCount_cast_succ]
  rw [lintegral_add_left (queryCount_cast_measurable A n)]
  rw [←lintegral_map (liveIndicator_measurable A) (measurable_pi_apply n),
    trajectoryLaw_endpoint A R ρ start hs h₀ n]

include hs in
theorem finite_calls_and_potential (V : S × H → ℝ≥0∞) (hV : Measurable V)
    (hstep : ∀ z,liveIndicator A z+(∫⁻ z',V z' ∂HistoryProgram.step A R z)≤V z)
    (n : ℕ) :
    (∫⁻ w,(queryCount A n w:ℝ≥0∞) ∂trajectoryLaw A R ρ start h₀)+
      (∫⁻ z,V z ∂runLaw A R ρ start h₀ n)≤ initialValue ρ start h₀ V := by
  induction n with
  | zero =>
      simp only [queryCount,Nat.cast_zero,lintegral_zero,zero_add]
      exact (runLaw_initial_integral A R ρ start hs h₀ V hV).le
  | succ n ih =>
      rw [queryCount_integral_succ A R ρ start hs h₀ n,runLaw_succ,
        Measure.lintegral_bind (Kernel.measurable _).aemeasurable hV.aemeasurable,add_assoc,
        ←lintegral_add_left (liveIndicator_measurable A)]
      exact (add_le_add_left (lintegral_mono hstep) _).trans ih

include hs in
/-- A genuine one-step call potential bounds the extended first-halt cost.
Nontermination costs infinity and is therefore excluded by a finite bound. -/
theorem stopped_calls_le_initial (V : S × H → ℝ≥0∞) (hV : Measurable V)
    (hstep : ∀ z,liveIndicator A z+(∫⁻ z',V z' ∂HistoryProgram.step A R z)≤V z) :
    (∫⁻ w,HistoryProgram.totalCalls A w ∂trajectoryLaw A R ρ start h₀)≤
      initialValue ρ start h₀ V := by
  have hg : ∀ᵐ w ∂trajectoryLaw A R ρ start h₀,HaltSticky A w := by
    have ht := ae_all_iff.mpr (fun n => trajectoryLaw_step_good A R ρ start h₀
      (fun _ => (0:ℝ)) measurable_const n)
    exact ht.mono (fun _ hw n hn => (hw n hn).1)
  have hm : Monotone (fun n => fun w : HistoryProgram.Path S H => (queryCount A n w:ℝ≥0∞)) := by
    intro n m hnm w
    exact Nat.cast_le.mpr (queryCount_mono A w hnm)
  calc
    _ = ∫⁻ w,⨆ n : ℕ,(queryCount A n w:ℝ≥0∞) ∂trajectoryLaw A R ρ start h₀ :=
      lintegral_congr_ae (hg.mono (fun w hw => totalCalls_eq_iSup_queryCount A w hw))
    _ = ⨆ n : ℕ,∫⁻ w,(queryCount A n w:ℝ≥0∞) ∂trajectoryLaw A R ρ start h₀ :=
      lintegral_iSup (queryCount_cast_measurable A) hm
    _ ≤ _ := by
      apply iSup_le
      intro n
      exact (le_add_right le_rfl).trans (finite_calls_and_potential A R ρ start hs h₀ V hV hstep n)

include hs in
/-- A nonnegative terminal-loss potential bounds actual stopped risk once
finite actual call cost has ruled out the nonterminating fallback. -/
theorem stopped_loss_le_initial (V : S × H → ℝ≥0∞) (hV : Measurable V)
    (hstep : ∀ z,(∫⁻ z',V z' ∂HistoryProgram.step A R z)≤V z)
    (loss : Y → ℝ) (hloss : Measurable loss)
    (hhalt : ∀ z,A.halt z.1=true → ENNReal.ofReal (loss (A.output z.1))≤V z)
    (hcost : (∫⁻ w,HistoryProgram.totalCalls A w ∂trajectoryLaw A R ρ start h₀)≠⊤) :
    (∫⁻ w,ENNReal.ofReal (loss (HistoryProgram.stoppedOutput A w))
      ∂trajectoryLaw A R ρ start h₀)≤ initialValue ρ start h₀ V := by
  let v : S → ℝ := loss ∘ A.output
  have hv : Measurable v := hloss.comp A.output_measurable
  have hg : ∀ᵐ w ∂trajectoryLaw A R ρ start h₀,∀ n,pathStepGood A v n w :=
    ae_all_iff.mpr (fun n => trajectoryLaw_step_good A R ρ start h₀ v hv n)
  change (∫⁻ w,ENNReal.ofReal (v (w (HistoryProgram.stopTime A w)).1)
    ∂trajectoryLaw A R ρ start h₀)≤_
  rw [stoppedValue_integral_eq_iSup A _ v hv hg
    (HistoryProgram.ae_terminated_of_cost_finite A _ hcost)]
  apply iSup_le
  intro n
  calc
    _ ≤ ∫⁻ w,V (w n) ∂trajectoryLaw A R ρ start h₀ := by
      apply lintegral_mono
      intro w
      by_cases hh : A.halt (w n).1=true
      · exact (show revealedLoss A v n w=ENNReal.ofReal (loss (A.output (w n).1)) by
          simp only [revealedLoss,hh,if_true,v,Function.comp_apply]) ▸ hhalt (w n) hh
      · simp only [revealedLoss,hh,if_false]
        exact bot_le
    _ = ∫⁻ z,V z ∂runLaw A R ρ start h₀ n := by
      rw [←lintegral_map hV (measurable_pi_apply n),trajectoryLaw_endpoint A R ρ start hs h₀ n]
    _ ≤ _ := finite_potential_bound A R ρ start hs h₀ V hV hstep n

end Bilevel.PolishedCompiledHistory
