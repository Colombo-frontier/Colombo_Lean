import GradientHessian.AugmentedNumericalPostprocessor
import GradientHessian.AugmentedNumericalExecution
import GradientHessian.AugmentedNumericalPreprocessor
import GradientHessian.SelectionCappedProgram

/-! Augmented postprocessing after the target forcing direction is supplied.
Initialization is still suspended when the target was initially active. Each
normal ordinary point is selected before feedback, with separately capped
matrix products and selected tests. -/

noncomputable section
namespace GradientHessian.AugmentedNumericalPostExecution
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

def withCursor (s : Run) (q : Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t) : Run :=
  ((s.1.1,s.1.2.1,q),s.2.1,false)

def advance (K : ℝ) (cutoff : ℕ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ) (s : Run) : Run :=
  withCursor t s (AugmentedNumericalExecution.fullCursor P B fallback t leaf policy K cutoff
    (taskDisclosed leaf j) s.1.1.2.2 s.1.1.2.1 (cache t B j s) A s.1.2.2)

def next (K : ℝ) (cutoff : ℕ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ) (s : Run) : Run :=
  if halt t leaf j s then s else advance t P B fallback leaf policy K cutoff j A s

def macroTime (s : Run) : ℕ := if normalInstruction t s.1.2.2 then 2 else 1

theorem step_advance {K : ℝ} (hK : 0<K) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (s : Run) (hh : halt t leaf j s=false)
    (hselected : normalInstruction t s.1.2.2=false ∨ s.2.2=true) :
    (program t P B fallback leaf policy hK cutoff j).step A s=advance t P B fallback leaf policy K cutoff j A s := by
  have hn : (normalInstruction t s.1.2.2 && !s.2.2)=false := by
    rcases hselected with h | h <;> simp [h]
  have hs := AugmentedNumericalExecution.one_product_cursor P B fallback t leaf policy K cutoff
    (taskDisclosed leaf j) s.1.1.2.2 s.1.1.2.1 (cache t B j s) A s.1.2.2
  cases hp : product t leaf (taskDisclosed leaf j) s.1.2.2 with
  | false =>
      simp only [hp,Bool.false_eq_true,if_false] at hs
      simp only [TestSelectionMachine.Program.step,program,mode,hh,hn,hp,Bool.false_eq_true,
        if_false,Fin.isValue,one_ne_zero,if_true,stepReply,advance,withCursor]
      exact congrArg (fun q => ((s.1.1,s.1.2.1,q),s.2.1,false)) hs
  | true =>
      simp only [hp,if_true] at hs
      simp only [TestSelectionMachine.Program.step,program,mode,hh,hn,hp,Bool.false_eq_true,
        if_false,Fin.isValue,reduceCtorEq,if_true,stepReply,query,AugmentedNumericalPreprocessor.query,advance,withCursor]
      rw [AugmentedNumericalEquality.product_coordinates]
      exact congrArg (fun q => ((s.1.1,s.1.2.1,q),s.2.1,false)) hs

theorem step_select {K : ℝ} (hK : 0<K) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (s : Run) (hh : halt t leaf j s=false)
    (hn : normalInstruction t s.1.2.2=true) (hb : s.2.2=false) :
    (program t P B fallback leaf policy hK cutoff j).mode s=3 ∧
      (program t P B fallback leaf policy hK cutoff j).step A s=selected t s := by
  simp [program,mode,hh,hn,hb,TestSelectionMachine.Program.step]

theorem run_macro {K : ℝ} (hK : 0<K) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (s : Run) (hb : s.2.2=false) :
    (program t P B fallback leaf policy hK cutoff j).run A (macroTime t s) s=
      next t P B fallback leaf policy K cutoff j A s := by
  cases hh : halt t leaf j s with
  | true =>
      have hm : (program t P B fallback leaf policy hK cutoff j).mode s=0 := by simp [program,mode,hh]
      have hf : (program t P B fallback leaf policy hK cutoff j).step A s=s := by
        simp only [TestSelectionMachine.Program.step,hm,if_true]
      simpa only [TestSelectionMachine.Program.run,next,hh,if_true] using
        Function.iterate_fixed hf (macroTime t s)
  | false =>
      cases hn : normalInstruction t s.1.2.2 with
      | false =>
          simpa only [macroTime,hn,Bool.false_eq_true,if_false,TestSelectionMachine.Program.run,
            Function.iterate_one,next,hh] using step_advance t P B fallback leaf policy hK cutoff j A s hh (Or.inl hn)
      | true =>
          have hfirst := (step_select t P B fallback leaf policy hK cutoff j A s hh hn hb).2
          have hsecond := step_advance t P B fallback leaf policy hK cutoff j A (selected t s)
            (by simpa only [halt,selected] using hh) (Or.inr rfl)
          simp only [macroTime,hn,if_true,TestSelectionMachine.Program.run,Function.iterate_succ_apply',
            Function.iterate_zero,Function.id_def,next,hh,Bool.false_eq_true,if_false]
          rw [hfirst,hsecond]
          rfl

theorem next_flag {K : ℝ} (cutoff : ℕ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : Run) (hb : s.2.2=false) :
    (next t P B fallback leaf policy K cutoff j A s).2.2=false := by
  unfold next
  split_ifs
  · exact hb
  · rfl

theorem next_cache (K : ℝ) (cutoff : ℕ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ) (s : Run) :
    cache t B j (next t P B fallback leaf policy K cutoff j A s)=cache t B j s := by
  unfold next
  split_ifs <;> rfl

end GradientHessian.AugmentedNumericalPostExecution
