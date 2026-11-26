import Bilevel.PolishedCompiledHistoryPotentials

/-! A continuation kernel records the remaining result, hidden history and
original calls at each valid compiled state. Its equations are operational
one-call equations, including the actual hidden-history update. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedCompiledHistory
open OracleCode Stateful HistoryProgram PolishedHistory
set_option autoImplicit false
variable {Q O A B C H : Space}

def increment (z : Outcome B H) : Outcome B H := (z.1,z.2.1,z.2.2+1)

theorem increment_measurable : Measurable (increment (B:=B) (H:=H)) :=
  measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
    ((measurable_snd.comp measurable_snd).add_const 1))

structure Summary (m : Machine Q O A B) (c : Code Q O A B) (R : HistoryProgram.Oracle Q O H) where
  remaining : Procedure m.state H B
  valid : Set m.state
  valid_measurable : MeasurableSet valid
  start_valid : ∀ a,m.start a∈valid
  update_valid : ∀ s,s∈valid → ∀ o,m.program.update (s,o)∈valid
  start_law : ∀ a h,remaining.law (m.start a,h)=(OracleCode.History.denote R.law R.update R.update_measurable c).law (a,h)
  halt_law : ∀ s,s∈valid → ∀ h,m.program.halt s=true →
    remaining.law (s,h)=Measure.dirac (m.program.output s,h,0)
  live_law : ∀ s,s∈valid → ∀ h,m.program.halt s=false →
    remaining.law (s,h)=((remaining.law ∘ₖ HistoryProgram.liveStep m.program R).map increment) (s,h)

namespace Summary
variable {m : Machine Q O A B} {c : Code Q O A B} {R : HistoryProgram.Oracle Q O H}
  (T : Summary m c R)

def potential (f : Outcome B H → ℝ≥0∞) (z : m.state × H) : ℝ≥0∞ := by
  classical
  exact if z.1∈T.valid then ∫⁻ y,f y ∂T.remaining.law z else ⊤

theorem potential_measurable (f : Outcome B H → ℝ≥0∞) (hf : Measurable f) :
    Measurable (T.potential f) :=
  hf.lintegral_kernel.ite (T.valid_measurable.preimage measurable_fst) measurable_const

theorem potential_start (f : Outcome B H → ℝ≥0∞) (a : A) (h : H) :
    T.potential f (m.start a,h)=∫⁻ y,f y ∂(OracleCode.History.denote R.law R.update R.update_measurable c).law (a,h) := by
  rw [potential,if_pos (T.start_valid a),T.start_law]

theorem live_potential_integral (f : Outcome B H → ℝ≥0∞) (hf : Measurable f)
    (s : m.state) (hs : s∈T.valid) (h : H) (hlive : m.program.halt s=false) :
    (∫⁻ z',T.potential f z' ∂HistoryProgram.step m.program R (s,h))=
      ∫⁻ o,∫⁻ y,f y ∂T.remaining.law
        (m.program.update (s,o),R.update ((m.program.query s,h),o)) ∂R.law (m.program.query s,h) := by
  classical
  have hadv : Measurable (fun o : O => HistoryProgram.advance m.program R ((s,h),o)) :=
    (HistoryProgram.advance_measurable m.program R).comp (measurable_const.prodMk measurable_id)
  rw [HistoryProgram.step_live _ _ _ hlive,
    lintegral_map (T.potential_measurable f hf)
      hadv]
  apply lintegral_congr
  intro o
  change (if m.program.update (s,o)∈T.valid then _ else _) = _
  rw [if_pos (T.update_valid s hs o)]
  rfl

theorem remaining_live_integral (f : Outcome B H → ℝ≥0∞) (hf : Measurable f)
    (s : m.state) (hs : s∈T.valid) (h : H) (hlive : m.program.halt s=false) :
    (∫⁻ y,f y ∂T.remaining.law (s,h))=
      ∫⁻ o,∫⁻ y,f (increment y) ∂T.remaining.law
        (m.program.update (s,o),R.update ((m.program.query s,h),o)) ∂R.law (m.program.query s,h) := by
  have hadv : Measurable (fun o : O => HistoryProgram.advance m.program R ((s,h),o)) :=
    (HistoryProgram.advance_measurable m.program R).comp (measurable_const.prodMk measurable_id)
  have hinner : Measurable (fun z => ∫⁻ y,f (increment y) ∂T.remaining.law z) :=
    (hf.comp increment_measurable).lintegral_kernel
  rw [T.live_law s hs h hlive,Kernel.lintegral_map _ increment_measurable _ hf,
    show (∫⁻ y,f (increment y) ∂(T.remaining.law ∘ₖ liveStep m.program R) (s,h))=
      (∫⁻ z,∫⁻ y,f (increment y) ∂T.remaining.law z ∂liveStep m.program R (s,h)) from
      Kernel.lintegral_comp _ _ _ (hf.comp increment_measurable),HistoryProgram.liveStep_apply,
    lintegral_map hinner
      hadv]
  rfl

def callPotential : m.state × H → ℝ≥0∞ := T.potential (fun y => (y.2.2:ℝ≥0∞))

theorem callPotential_measurable : Measurable T.callPotential :=
  T.potential_measurable _ ((measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp
    (measurable_snd.comp measurable_snd))

theorem callPotential_step (z : m.state × H) :
    liveIndicator m.program z+(∫⁻ z',T.callPotential z' ∂HistoryProgram.step m.program R z)≤T.callPotential z := by
  rcases z with ⟨s,h⟩
  by_cases hs : s∈T.valid
  · cases hh : m.program.halt s with
    | true =>
        rw [HistoryProgram.step_halted _ _ _ hh,lintegral_dirac' _ T.callPotential_measurable]
        simp only [liveIndicator,hh,if_true,zero_add,le_refl]
    | false =>
        have hf : Measurable (fun y : Outcome B H => (y.2.2:ℝ≥0∞)) :=
          (measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp (measurable_snd.comp measurable_snd)
        change liveIndicator m.program (s,h)+(∫⁻ z',T.potential _ z' ∂_)≤T.potential _ (s,h)
        rw [T.live_potential_integral _ hf s hs h hh,potential,if_pos hs,
          T.remaining_live_integral _ hf s hs h hh]
        simp only [liveIndicator,hh,Bool.false_eq_true,if_false,increment,Nat.cast_add,Nat.cast_one]
        simp_rw [lintegral_add_right _ measurable_const,lintegral_const,measure_univ,mul_one]
        rw [lintegral_add_right _ measurable_const,lintegral_const,measure_univ,mul_one,add_comm]
  · simp only [callPotential,potential,if_neg hs]
    exact le_top

def lossPotential (loss : B → ℝ) : m.state × H → ℝ≥0∞ :=
  T.potential (fun y => ENNReal.ofReal (loss y.1))

theorem lossPotential_measurable (loss : B → ℝ) (hloss : Measurable loss) :
    Measurable (T.lossPotential loss) := T.potential_measurable _ (hloss.comp measurable_fst).ennreal_ofReal

theorem lossPotential_step (loss : B → ℝ) (hloss : Measurable loss) (z : m.state × H) :
    (∫⁻ z',T.lossPotential loss z' ∂HistoryProgram.step m.program R z)≤T.lossPotential loss z := by
  rcases z with ⟨s,h⟩
  by_cases hs : s∈T.valid
  · cases hh : m.program.halt s with
    | true => exact (by rw [HistoryProgram.step_halted _ _ _ hh,
        lintegral_dirac' _ (T.lossPotential_measurable loss hloss)])
    | false =>
        have hf : Measurable (fun y : Outcome B H => ENNReal.ofReal (loss y.1)) :=
          (hloss.comp measurable_fst).ennreal_ofReal
        change (∫⁻ z',T.potential _ z' ∂_)≤T.potential _ (s,h)
        rw [T.live_potential_integral _ hf s hs h hh,potential,if_pos hs,
          T.remaining_live_integral _ hf s hs h hh]
        exact le_rfl
  · simp only [lossPotential,potential,if_neg hs]
    exact le_top

theorem lossPotential_halt (loss : B → ℝ) (hloss : Measurable loss)
    (z : m.state × H) (hh : m.program.halt z.1=true) :
    ENNReal.ofReal (loss (m.program.output z.1))≤T.lossPotential loss z := by
  have hf : Measurable (fun y : Outcome B H => ENNReal.ofReal (loss y.1)) :=
    (hloss.comp measurable_fst).ennreal_ofReal
  by_cases hs : z.1∈T.valid
  · rw [lossPotential,potential,if_pos hs,T.halt_law z.1 hs z.2 hh,lintegral_dirac' _ hf]
  · simp only [lossPotential,potential,if_neg hs]
    exact le_top

include T in
/-- Expected original calls of the actual compiled program are bounded by
its continuation denotation, averaged over arbitrary private input. -/
theorem stopped_calls_le_denote (ρ : Measure A) (h₀ : H) :
    (∫⁻ w,HistoryProgram.totalCalls m.program w
      ∂trajectoryLaw m.program R ρ m.start h₀)≤
    ∫⁻ a,∫⁻ y,(y.2.2:ℝ≥0∞)
      ∂(OracleCode.History.denote R.law R.update R.update_measurable c).law (a,h₀) ∂ρ := by
  have hb := stopped_calls_le_initial m.program R ρ m.start m.start_measurable h₀
    T.callPotential T.callPotential_measurable T.callPotential_step
  simpa only [initialValue,callPotential,T.potential_start] using hb

include T in
/-- The actual stopped risk is bounded by the compositional denotation;
finite denotation call cost establishes actual almost-sure termination. -/
theorem stopped_loss_le_denote (ρ : Measure A) (h₀ : H)
    (hcost : (∫⁻ a,∫⁻ y,(y.2.2:ℝ≥0∞)
      ∂(OracleCode.History.denote R.law R.update R.update_measurable c).law (a,h₀) ∂ρ)≠⊤)
    (loss : B → ℝ) (hloss : Measurable loss) :
    (∫⁻ w,ENNReal.ofReal (loss (HistoryProgram.stoppedOutput m.program w))
      ∂trajectoryLaw m.program R ρ m.start h₀)≤
    ∫⁻ a,∫⁻ y,ENNReal.ofReal (loss y.1)
      ∂(OracleCode.History.denote R.law R.update R.update_measurable c).law (a,h₀) ∂ρ := by
  have hc : (∫⁻ w,HistoryProgram.totalCalls m.program w
      ∂trajectoryLaw m.program R ρ m.start h₀)≠⊤ :=
    ne_top_of_le_ne_top hcost (T.stopped_calls_le_denote ρ h₀)
  have hb := stopped_loss_le_initial m.program R ρ m.start m.start_measurable h₀
    (T.lossPotential loss) (T.lossPotential_measurable loss hloss)
    (T.lossPotential_step loss hloss) loss hloss (T.lossPotential_halt loss hloss) hc
  simpa only [initialValue,lossPotential,T.potential_start] using hb

end Summary
end Bilevel.PolishedCompiledHistory
