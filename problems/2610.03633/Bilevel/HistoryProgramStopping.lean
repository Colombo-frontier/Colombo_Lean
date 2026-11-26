import Bilevel.HistoryProgram
import Bilevel.BorelAdaptiveExtendedCalls

/-! First-halt output and extended original-call count on a full execution
trajectory. Nontermination costs infinity, exactly as in the fresh-seed
model. These definitions apply to every measurable adaptive program. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.HistoryProgram
set_option autoImplicit false
variable {S Q O Y H : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y] [MeasurableSpace H]
variable (A : BorelAdaptive.Program S Q O Y)

abbrev Path (S H : Type*) := ℕ → S × H

def Terminated (w : Path S H) : Prop := ∃ n,A.halt (w n).1=true

theorem terminated_measurable : MeasurableSet {w : Path S H | Terminated A w} := by
  have hn (n : ℕ) : MeasurableSet {w : Path S H | A.halt (w n).1=true} :=
    (A.halt_measurable.comp (measurable_fst.comp (measurable_pi_apply n)))
      (measurableSet_singleton true)
  simpa only [Terminated,Set.iUnion_setOf] using MeasurableSet.iUnion hn

open Classical in
def stopTime (w : Path S H) : ℕ := if hw : Terminated A w then Nat.find hw else 0

theorem stopTime_measurable : Measurable (stopTime A (H:=H)) := by
  classical
  let T := {w : Path S H | Terminated A w}
  have hm : Measurable (fun w : T => Nat.find w.property) := by
    apply measurable_find (fun w : T => w.property)
    intro n
    have hn : Measurable (fun w : Path S H => A.halt (w n).1) :=
      A.halt_measurable.comp (measurable_fst.comp (measurable_pi_apply n))
    exact (hn.comp measurable_subtype_coe) (measurableSet_singleton true)
  exact hm.dite measurable_const (terminated_measurable A)

omit [MeasurableSpace H] in
theorem stopTime_halted (w : Path S H) (hw : Terminated A w) :
    A.halt (w (stopTime A w)).1=true := by
  simp only [stopTime,dif_pos hw]
  exact Nat.find_spec hw

omit [MeasurableSpace H] in
theorem stopTime_first (w : Path S H) (hw : Terminated A w) (n : ℕ)
    (hn : n<stopTime A w) : A.halt (w n).1=false := by
  rw [stopTime,dif_pos hw] at hn
  exact Bool.eq_false_of_not_eq_true (Nat.find_min hw hn)

def stoppedOutput (w : Path S H) : Y := A.output (w (stopTime A w)).1

theorem stoppedOutput_measurable : Measurable (stoppedOutput A (H:=H)) := by
  have hm : Measurable (fun z : Path S H × ℕ => A.output (z.1 z.2).1) :=
    measurable_from_prod_countable (fun n =>
      A.output_measurable.comp (measurable_fst.comp (measurable_pi_apply n)))
  exact hm.comp (measurable_id.prodMk (stopTime_measurable A))

open Classical in
def totalCalls (w : Path S H) : ℝ≥0∞ := if Terminated A w then (stopTime A w:ℝ≥0∞) else ⊤

theorem totalCalls_measurable : Measurable (totalCalls A (H:=H)) := by
  classical
  exact ((measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp
    (stopTime_measurable A)).ite (terminated_measurable A) measurable_const

omit [MeasurableSpace H] in
theorem totalCalls_eq_top_iff (w : Path S H) : totalCalls A w=⊤ ↔ ¬Terminated A w := by
  classical
  by_cases h : Terminated A w <;> simp [totalCalls,h]

theorem ae_terminated_of_cost_finite (ν : Measure (Path S H))
    (hc : (∫⁻ w,totalCalls A w ∂ν)≠⊤) : ∀ᵐ w ∂ν,Terminated A w := by
  filter_upwards [ae_lt_top (totalCalls_measurable A) hc] with w hw
  exact not_not.mp (fun hn => hw.ne ((totalCalls_eq_top_iff A w).mpr hn))

/- Reading a deterministic fresh-seed execution as a trajectory does not
alter its stopping event, first stopping time, terminal output, or calls. -/
omit [MeasurableSpace H] in
theorem fresh_terminated {C : Type*} (reply : Unit → Q → C → O)
    (s : S) (draws : ℕ → C) (h : H) :
    Terminated A (fun n => (BorelAdaptive.run A reply () draws s n,h)) ↔
      BorelAdaptive.Terminated A reply ((),s,draws) := Iff.rfl

omit [MeasurableSpace H] in
theorem fresh_stopTime {C : Type*} (reply : Unit → Q → C → O)
    (s : S) (draws : ℕ → C) (h : H) :
    stopTime A (fun n => (BorelAdaptive.run A reply () draws s n,h))=
      BorelAdaptive.stopTime A reply ((),s,draws) := rfl

omit [MeasurableSpace H] in
theorem fresh_stoppedOutput {C : Type*} (reply : Unit → Q → C → O)
    (s : S) (draws : ℕ → C) (h : H) :
    stoppedOutput A (fun n => (BorelAdaptive.run A reply () draws s n,h))=
      BorelAdaptive.stoppedOutput A reply ((),s,draws) := rfl

omit [MeasurableSpace H] in
theorem fresh_totalCalls {C : Type*} (reply : Unit → Q → C → O)
    (s : S) (draws : ℕ → C) (h : H) :
    totalCalls A (fun n => (BorelAdaptive.run A reply () draws s n,h))=
      BorelAdaptive.totalCalls A reply ((),s,draws) := rfl

end Bilevel.HistoryProgram
