import Bilevel.CappedExecution
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Measurability of the actual cap controller and its terminal output. -/
noncomputable section
open MeasureTheory
namespace Bilevel.CappedExecution

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

theorem run_measurable (Λ cap : ℝ) (x₀ : E) (G : ℕ → Ω → E)
    (hG : ∀ i, Measurable (G i)) (n : ℕ) :
    Measurable (fun ω => (run Λ cap x₀ (fun i => G i ω) n).point) ∧
    Measurable (fun ω => (run Λ cap x₀ (fun i => G i ω) n).energy) ∧
    Measurable (fun ω => (run Λ cap x₀ (fun i => G i ω) n).stopped) := by
  classical
  induction n with
  | zero => exact ⟨measurable_const, measurable_const, measurable_const⟩
  | succ n ih =>
    let s := fun ω => run Λ cap x₀ (fun i => G i ω) n
    have hp : Measurable (fun ω => (s ω).point) := ih.1
    have he : Measurable (fun ω => (s ω).energy) := ih.2.1
    have hs : Measurable (fun ω => (s ω).stopped) := ih.2.2
    have hstop : MeasurableSet {ω | (s ω).stopped = true} := hs (measurableSet_singleton true)
    have henergy : Measurable (fun ω => (s ω).energy+‖G n ω‖^2) := he.add ((hG n).norm.pow_const 2)
    have haccept : MeasurableSet {ω | (s ω).energy+‖G n ω‖^2 ≤ cap} :=
      measurableSet_le henergy measurable_const
    have hpoint : Measurable (fun ω => if (s ω).stopped = true then (s ω).point else
        if (s ω).energy+‖G n ω‖^2 ≤ cap then (s ω).point-Λ⁻¹ • G n ω else (s ω).point) :=
      hp.ite hstop ((hp.sub ((hG n).const_smul (Λ⁻¹))).ite haccept hp)
    have henergy' : Measurable (fun ω => if (s ω).stopped = true then (s ω).energy else
        if (s ω).energy+‖G n ω‖^2 ≤ cap then (s ω).energy+‖G n ω‖^2 else (s ω).energy) :=
      he.ite hstop (henergy.ite haccept he)
    have hstop' : Measurable (fun ω => if (s ω).stopped = true then (s ω).stopped else
        if (s ω).energy+‖G n ω‖^2 ≤ cap then false else true) := hs.ite hstop
      ((measurable_const : Measurable (fun _ : Ω => false)).ite haccept measurable_const)
    constructor
    · convert hpoint using 1
      funext ω
      simp only [run, step, s]
      split_ifs <;> rfl
    constructor
    · convert henergy' using 1
      funext ω
      simp only [run, step, s]
      split_ifs <;> rfl
    · convert hstop' using 1
      funext ω
      simp only [run, step, s]
      split_ifs <;> rfl

theorem output_measurable (Λ cap : ℝ) (x₀ : E) (G : ℕ → Ω → E)
    (hG : ∀ i, Measurable (G i)) (N index : ℕ) :
    Measurable (fun ω => output Λ cap x₀ (fun i => G i ω) N index) := by
  classical
  have hstop := (run_measurable Λ cap x₀ G hG N).2.2
  have hp := (run_measurable Λ cap x₀ G hG index).1
  exact measurable_const.ite (hstop (measurableSet_singleton true)) hp

end Bilevel.CappedExecution
