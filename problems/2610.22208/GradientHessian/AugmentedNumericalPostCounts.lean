import GradientHessian.AugmentedNumericalPostClock
import GradientHessian.SelectionCapTransparency
import GradientHessian.AugmentedNumericalPostExecution
import GradientHessian.AugmentedNumericalPostprocessor
import GradientHessian.AugmentedNumericalExecution
import GradientHessian.AugmentedNumericalPreprocessor
import GradientHessian.SelectionCappedProgram

/-! Augmented postprocessing after the target forcing direction is supplied.
Initialization is still suspended when the target was initially active. Each
normal ordinary point is selected before feedback, with separately capped
matrix products and selected tests. -/

noncomputable section
namespace GradientHessian.AugmentedNumericalPostCounts
open Classical HigherHierarchy HierarchyAddresses FrontierState TaskState
  NumericalCachedOracle AugmentedNumericalDriver

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (t : ℕ)
variable [MeasurableSpace (DirectionPolicyReplay.Point d J E H t)]
  [BorelSpace (DirectionPolicyReplay.Point d J E H t)]
  [MeasurableSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [BorelSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [MeasurableSpace (DirectionPolicyReplay.Rich d J E H t)]
  [BorelSpace (DirectionPolicyReplay.Rich d J E H t)]

abbrev RuntimeState := AugmentedNumericalPreprocessor.RuntimeState
  (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t ×
    EuclideanSpace ℝ (Fin r) × Bool

local notation "Pre" => AugmentedNumericalPreprocessor.RuntimeState (d := d) (n := n) (r := r)
  (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t
local notation "Run" => RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
  (E := E) (H := H) (Seed := Seed) (S := S) t

variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (leaf : Leaf (t+1))
  (policy : Machine.Policy (Seed × AugmentedPolicy.Packet d J E H t ell) S
    (DirectionPolicyReplay.Point d J E H t)
    (AugmentedPolicy.Ordinary d J E H t ell) (AugmentedPolicy.Rich d J E H t ell))

open Matrix ComparisonControllerReplay AugmentedNumericalPostprocessor

open AugmentedNumericalPostExecution
open AugmentedNumericalPostClock SelectionCapTransparency
def queryBit (j : Fin (4096*J^2+1))
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) : ℕ :=
  if halt t leaf j s then 0 else
    if AugmentedNumericalDriver.product t leaf (taskDisclosed leaf j) s.1.2.2 then 1 else 0

def selectionBit (j : Fin (4096*J^2+1))
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) : ℕ :=
  if halt t leaf j s then 0 else if normalInstruction t s.1.2.2 then 1 else 0

theorem normal_product_false (j : Fin (4096*J^2+1))
    (q : AugmentedNumericalDriver.Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t)
    (hn : normalInstruction t q=true) :
    AugmentedNumericalDriver.product t leaf (taskDisclosed leaf j) q=false := by
  cases q with
  | inl star => cases hn
  | inr q =>
      cases q with
      | ready => cases hn
      | finished => cases hn
      | pending n a output phase =>
          cases phase with
          | repairing => cases hn
          | delivered => cases hn
          | frozen => cases hn
          | normal => rfl
theorem queryCount_macro {K : ℝ} (hK : 0<K) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false) :
    (program t P B fallback leaf policy hK cutoff j).queryCount A (macroTime t s) s=queryBit t leaf j s := by
  cases hh : halt t leaf j s with
  | true =>
      have hm : (program t P B fallback leaf policy hK cutoff j).mode s=0 := by simp [program,mode,hh]
      have hf : (program t P B fallback leaf policy hK cutoff j).step A s=s := by
        simp only [TestSelectionMachine.Program.step,hm,if_true]
      simp [TestSelectionMachine.Program.queryCount,TestSelectionMachine.Program.run,
        Function.iterate_fixed hf,hm,queryBit,hh]
  | false =>
      cases hn : normalInstruction t s.1.2.2 with
      | false =>
          cases hp : AugmentedNumericalDriver.product t leaf (taskDisclosed leaf j) s.1.2.2 <;>
            simp only [macroTime,hn,Bool.false_eq_true,if_false]
          all_goals rw [queryCount_succ _ A 0 s]
          all_goals simp [TestSelectionMachine.Program.queryCount,TestSelectionMachine.Program.run,
            program,mode,hh,hn,hp,queryBit]
      | true =>
          have hp := normal_product_false t leaf j _ hn
          have hfirst := (step_select t P B fallback leaf policy hK cutoff j A s hh hn hb).2
          have hm : (program t P B fallback leaf policy hK cutoff j).mode s=3 :=
            (step_select t P B fallback leaf policy hK cutoff j A s hh hn hb).1
          have hm' : (program t P B fallback leaf policy hK cutoff j).mode (AugmentedNumericalPostprocessor.selected t s)=1 := by
            change (if halt t leaf j s then 0 else if normalInstruction t s.1.2.2 && !true then 3 else
              if AugmentedNumericalDriver.product t leaf (taskDisclosed leaf j) s.1.2.2 then 2 else 1)=1
            simp [hh,hn,hp]
          rw [show macroTime t s=2 by simp [macroTime,hn],
            queryCount_succ _ A 1 s,queryCount_succ _ A 0 s]
          simp [TestSelectionMachine.Program.queryCount,TestSelectionMachine.Program.run,
            hfirst,hm,hm',queryBit,hh,hp]

theorem selections_macro {K : ℝ} (hK : 0<K) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false) :
    (program t P B fallback leaf policy hK cutoff j).selections A (macroTime t s) s=selectionBit t leaf j s := by
  cases hh : halt t leaf j s with
  | true =>
      have hm : (program t P B fallback leaf policy hK cutoff j).mode s=0 := by simp [program,mode,hh]
      have hf : (program t P B fallback leaf policy hK cutoff j).step A s=s := by
        simp only [TestSelectionMachine.Program.step,hm,if_true]
      simp [selections_eq_sum,TestSelectionMachine.Program.run,Function.iterate_fixed hf,hm,selectionBit,hh]
  | false =>
      cases hn : normalInstruction t s.1.2.2 with
      | false =>
          cases hp : AugmentedNumericalDriver.product t leaf (taskDisclosed leaf j) s.1.2.2 <;>
            simp [macroTime,hn,TestSelectionMachine.Program.selections,TestSelectionMachine.Program.run,
              program,mode,hh,hn,hp,selectionBit]
      | true =>
          have hp := normal_product_false t leaf j _ hn
          have hfirst := (step_select t P B fallback leaf policy hK cutoff j A s hh hn hb).2
          have hm : (program t P B fallback leaf policy hK cutoff j).mode s=3 :=
            (step_select t P B fallback leaf policy hK cutoff j A s hh hn hb).1
          have hm' : (program t P B fallback leaf policy hK cutoff j).mode (AugmentedNumericalPostprocessor.selected t s)=1 := by
            change (if halt t leaf j s then 0 else if normalInstruction t s.1.2.2 && !true then 3 else
              if AugmentedNumericalDriver.product t leaf (taskDisclosed leaf j) s.1.2.2 then 2 else 1)=1
            simp [hh,hn,hp]
          simp [macroTime,hn,TestSelectionMachine.Program.selections,TestSelectionMachine.Program.run,
            Function.iterate_succ_apply',hfirst,hm,hm',selectionBit,hh]

theorem queryCount_clock {K : ℝ} (hK : 0<K) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false) (N : ℕ) :
    (program t P B fallback leaf policy hK cutoff j).queryCount A (clock t P B fallback leaf policy K cutoff j A N s) s=
      ∑ i∈Finset.range N,queryBit t leaf j ((next t P B fallback leaf policy K cutoff j A)^[i] s) := by
  induction N with
  | zero => simp [clock,TestSelectionMachine.Program.queryCount]
  | succ N ih =>
      rw [clock,queryCount_add,run_clock t P B fallback leaf policy hK cutoff j A s hb N,
        queryCount_macro t P B fallback leaf policy hK cutoff j A _
          (next_iterate_flag t P B fallback leaf policy K cutoff j A s hb N),ih,Finset.sum_range_succ]

theorem selections_clock {K : ℝ} (hK : 0<K) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false) (N : ℕ) :
    (program t P B fallback leaf policy hK cutoff j).selections A (clock t P B fallback leaf policy K cutoff j A N s) s=
      ∑ i∈Finset.range N,selectionBit t leaf j ((next t P B fallback leaf policy K cutoff j A)^[i] s) := by
  induction N with
  | zero => simp [clock,TestSelectionMachine.Program.selections]
  | succ N ih =>
      rw [clock,selections_add,run_clock t P B fallback leaf policy hK cutoff j A s hb N,
        selections_macro t P B fallback leaf policy hK cutoff j A _
          (next_iterate_flag t P B fallback leaf policy K cutoff j A s hb N),ih,Finset.sum_range_succ]

end GradientHessian.AugmentedNumericalPostCounts


