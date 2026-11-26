import Bilevel.PolishedHistoryStoppedComparison

/-! Complete stationary stopping-cost equivalence, and stopping-risk
equivalence whenever the expected original-call cost is finite. The latter
condition only removes the nontermination fallback from the loss. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveQuery HistoryProgram
set_option autoImplicit false
variable {G : Geometry} {μ L ρ Δ R₀ σf σg : ℝ}

variable (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg) (A : Algorithm G)

def seedPath (z : A.Private × IndependentStream.Stream I.Seed) :
    HistoryProgram.Path A.State Unit := fun n =>
  freshState (I.reply ()) A.program (A.start z.1) n z.2

theorem seedPath_measurable : Measurable (seedPath I A) :=
  measurable_pi_lambda _ (fun n =>
    (freshState_joint_measurable (I.reply ()) (stationary_reply_measurable I) A.program n).comp
      ((A.start_measurable.comp measurable_fst).prodMk measurable_snd))

def seedExecution : Measure (HistoryProgram.Path A.State Unit) :=
  (A.privateLaw.prod (IndependentStream.law I.law)).map (seedPath I A)

theorem execution_endpoint_eq_seed (n : ℕ) :
    ((ofStationary I).execution A).map (fun w => w n)=
      (seedExecution I A).map (fun w => w n) := by
  rw [seedExecution,Measure.map_map (measurable_pi_apply n) (seedPath_measurable I A)]
  exact ofStationary_execution_endpoint I A n

theorem seedPath_step_good (v : A.State → ℝ)
    (z : A.Private × IndependentStream.Stream I.Seed) (n : ℕ) :
    pathStepGood A.program v n (seedPath I A z) := by
  intro hh
  change A.program.halt (BorelAdaptive.run A.program I.reply () z.2 (A.start z.1) n)=true at hh
  have he := BorelAdaptive.step_halted A.program I.reply () (z.2 n)
    (BorelAdaptive.run A.program I.reply () z.2 (A.start z.1) n) hh
  change A.program.halt (BorelAdaptive.run A.program I.reply () z.2 (A.start z.1) (n+1))=true ∧
    v (BorelAdaptive.run A.program I.reply () z.2 (A.start z.1) (n+1))=
      v (BorelAdaptive.run A.program I.reply () z.2 (A.start z.1) n)
  simp only [BorelAdaptive.run,he]
  exact ⟨hh,trivial⟩

theorem seedExecution_step_good (v : A.State → ℝ) (hv : Measurable v) :
    ∀ᵐ w ∂seedExecution I A,∀ n,pathStepGood A.program v n w := by
  apply ae_all_iff.mpr
  intro n
  rw [seedExecution]
  exact (ae_map_iff (seedPath_measurable I A).aemeasurable
    (pathStepGood_measurable A.program v hv n)).mpr
      (Filter.Eventually.of_forall (fun z => seedPath_step_good I A v z n))

variable {I A}
theorem Instance.execution_step_good
    (I : Instance G μ L ρ Δ R₀ σf σg) (A : Algorithm G)
    (v : A.State → ℝ) (hv : Measurable v) :
    ∀ᵐ w ∂I.execution A,∀ n,pathStepGood A.program v n w := by
  apply ae_all_iff.mpr
  intro n
  exact trajectoryLaw_step_good A.program I.historyOracle A.privateLaw A.start I.initialHistory v hv n

/-- Same program, exact expected extended call count, including infinity. -/
theorem ofStationary_cost (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg)
    (A : Algorithm G) : (ofStationary I).cost A=I.cost A := by
  have hμ := (ofStationary I).execution_step_good A (fun _ => (0:ℝ)) measurable_const
  have hν := seedExecution_step_good I A (fun _ => (0:ℝ)) measurable_const
  have hsμ : ∀ᵐ w ∂(ofStationary I).execution A,HaltSticky A.program w :=
    hμ.mono (fun _ hw n hn => (hw n hn).1)
  have hsν : ∀ᵐ w ∂seedExecution I A,HaltSticky A.program w :=
    hν.mono (fun _ hw n hn => (hw n hn).1)
  calc
    _ = ∫⁻ w,HistoryProgram.totalCalls A.program w ∂seedExecution I A :=
      totalCalls_integral_eq A.program _ _ (execution_endpoint_eq_seed I A) hsμ hsν
    _ = _ := by
      rw [seedExecution,lintegral_map (HistoryProgram.totalCalls_measurable A.program)
        (seedPath_measurable I A)]
      rfl

/-- Actual stopped gradient risk is preserved for every finite-cost solver.
No accuracy property or oracle lower bound is assumed. -/
theorem ofStationary_risk_of_cost_finite (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg)
    (A : Algorithm G) (hc : (ofStationary I).cost A≠⊤) :
    (ofStationary I).risk A=I.risk A := by
  let v : A.State → ℝ := fun s => I.loss (A.program.output s)
  have hv : Measurable v := (ofStationary I).loss_measurable.comp A.program.output_measurable
  have hμ := (ofStationary I).execution_step_good A v hv
  have hν := seedExecution_step_good I A v hv
  have he := stoppedValue_integral_eq A.program ((ofStationary I).execution A)
    (seedExecution I A) (execution_endpoint_eq_seed I A) v hv hμ hν hc
  change (∫⁻ w,ENNReal.ofReal (v (w (HistoryProgram.stopTime A.program w)).1)
    ∂(ofStationary I).execution A)=_
  have hstop : Measurable (fun w : HistoryProgram.Path A.State Unit =>
      ENNReal.ofReal (v (w (HistoryProgram.stopTime A.program w)).1)) :=
    (((ofStationary I).loss_measurable.comp
      (HistoryProgram.stoppedOutput_measurable A.program)).ennreal_ofReal)
  rw [he,seedExecution]
  exact (lintegral_map hstop (seedPath_measurable I A)).trans (by rfl)

end Bilevel.PolishedHistory
