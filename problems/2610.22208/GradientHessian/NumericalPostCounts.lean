import GradientHessian.NumericalPostClock
import GradientHessian.SelectionCapTransparency
noncomputable section
namespace GradientHessian.NumericalPostCounts
open Classical HigherHierarchy HierarchyAddresses CensoredHierarchy FrontierState TaskState
  ComparisonController ComparisonControllerReplay ControllerMeasurable ControllerPolicyDriver
  GeometricRepair NumericalCachedOracle

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (leaf : Leaf (t+1))
variable [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (policy : Machine.Policy Seed S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
  (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))
  (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ)))

open Matrix NumericalPostprocessor NumericalPostExecution

open NumericalPostClock SelectionCapTransparency

def queryBit (j : Fin (4096*J^2+1))
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) : ℕ :=
  if halt t leaf j s then 0 else
    if NumericalDriverInstructions.product leaf (taskDisclosed leaf j) s.1.2.2 then 1 else 0

def selectionBit (j : Fin (4096*J^2+1))
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) : ℕ :=
  if halt t leaf j s then 0 else if normalInstruction t s.1.2.2 then 1 else 0

theorem normal_product_false (j : Fin (4096*J^2+1))
    (q : Config (t+1) (4096*J^2+1) ell S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
      (Action t (4096*J^2))) (hn : normalInstruction t q=true) :
    NumericalDriverInstructions.product leaf (taskDisclosed leaf j) q=false := by
  cases q with
  | ready => cases hn
  | finished => cases hn
  | pending n a output phase =>
    cases phase with
    | repairing => cases hn
    | delivered => cases hn
    | frozen => cases hn
    | normal => rfl

theorem queryCount_macro {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false) :
    (program P B fallback t leaf policy hK j).queryCount A (macroTime t s) s=queryBit t leaf j s := by
  cases hh : halt t leaf j s with
  | true =>
      have hm : (program P B fallback t leaf policy hK j).mode s=0 := by simp [program,mode,hh]
      have hf : (program P B fallback t leaf policy hK j).step A s=s := by
        simp only [TestSelectionMachine.Program.step,hm,if_true]
      simp [TestSelectionMachine.Program.queryCount,TestSelectionMachine.Program.run,
        Function.iterate_fixed hf,hm,queryBit,hh]
  | false =>
      cases hn : normalInstruction t s.1.2.2 with
      | false =>
          cases hp : NumericalDriverInstructions.product leaf (taskDisclosed leaf j) s.1.2.2 <;>
            simp only [macroTime,hn,Bool.false_eq_true,if_false]
          all_goals rw [queryCount_succ _ A 0 s]
          all_goals simp [TestSelectionMachine.Program.queryCount,TestSelectionMachine.Program.run,
            program,mode,hh,hn,hp,queryBit]
      | true =>
          have hp := normal_product_false t leaf j _ hn
          have hfirst := (step_select P B fallback t leaf policy hK j A s hh hn hb).2
          have hm : (program P B fallback t leaf policy hK j).mode s=3 :=
            (step_select P B fallback t leaf policy hK j A s hh hn hb).1
          have hm' : (program P B fallback t leaf policy hK j).mode (NumericalPostprocessor.selected t s)=1 := by
            change (if halt t leaf j s then 0 else if normalInstruction t s.1.2.2 && !true then 3 else
              if NumericalDriverInstructions.product leaf (taskDisclosed leaf j) s.1.2.2 then 2 else 1)=1
            simp [hh,hn,hp]
          rw [show macroTime t s=2 by simp [macroTime,hn],
            queryCount_succ _ A 1 s,queryCount_succ _ A 0 s]
          simp [TestSelectionMachine.Program.queryCount,TestSelectionMachine.Program.run,
            hfirst,hm,hm',queryBit,hh,hp]

theorem selections_macro {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false) :
    (program P B fallback t leaf policy hK j).selections A (macroTime t s) s=selectionBit t leaf j s := by
  cases hh : halt t leaf j s with
  | true =>
      have hm : (program P B fallback t leaf policy hK j).mode s=0 := by simp [program,mode,hh]
      have hf : (program P B fallback t leaf policy hK j).step A s=s := by
        simp only [TestSelectionMachine.Program.step,hm,if_true]
      simp [selections_eq_sum,TestSelectionMachine.Program.run,Function.iterate_fixed hf,hm,selectionBit,hh]
  | false =>
      cases hn : normalInstruction t s.1.2.2 with
      | false =>
          cases hp : NumericalDriverInstructions.product leaf (taskDisclosed leaf j) s.1.2.2 <;>
            simp [macroTime,hn,TestSelectionMachine.Program.selections,TestSelectionMachine.Program.run,
              program,mode,hh,hn,hp,selectionBit]
      | true =>
          have hp := normal_product_false t leaf j _ hn
          have hfirst := (step_select P B fallback t leaf policy hK j A s hh hn hb).2
          have hm : (program P B fallback t leaf policy hK j).mode s=3 :=
            (step_select P B fallback t leaf policy hK j A s hh hn hb).1
          have hm' : (program P B fallback t leaf policy hK j).mode (NumericalPostprocessor.selected t s)=1 := by
            change (if halt t leaf j s then 0 else if normalInstruction t s.1.2.2 && !true then 3 else
              if NumericalDriverInstructions.product leaf (taskDisclosed leaf j) s.1.2.2 then 2 else 1)=1
            simp [hh,hn,hp]
          simp [macroTime,hn,TestSelectionMachine.Program.selections,TestSelectionMachine.Program.run,
            Function.iterate_succ_apply',hfirst,hm,hm',selectionBit,hh]

theorem queryCount_clock {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false) (N : ℕ) :
    (program P B fallback t leaf policy hK j).queryCount A (clock P B fallback t leaf policy K j A N s) s=
      ∑ i∈Finset.range N,queryBit t leaf j ((next P B fallback t leaf policy K j A)^[i] s) := by
  induction N with
  | zero => simp [clock,TestSelectionMachine.Program.queryCount]
  | succ N ih =>
      rw [clock,queryCount_add,run_clock P B fallback t leaf policy hK j A s hb N,
        queryCount_macro P B fallback t leaf policy hK j A _
          (next_iterate_flag P B fallback t leaf policy K j A s hb N),ih,Finset.sum_range_succ]

theorem selections_clock {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false) (N : ℕ) :
    (program P B fallback t leaf policy hK j).selections A (clock P B fallback t leaf policy K j A N s) s=
      ∑ i∈Finset.range N,selectionBit t leaf j ((next P B fallback t leaf policy K j A)^[i] s) := by
  induction N with
  | zero => simp [clock,TestSelectionMachine.Program.selections]
  | succ N ih =>
      rw [clock,selections_add,run_clock P B fallback t leaf policy hK j A s hb N,
        selections_macro P B fallback t leaf policy hK j A _
          (next_iterate_flag P B fallback t leaf policy K j A s hb N),ih,Finset.sum_range_succ]

end GradientHessian.NumericalPostCounts

