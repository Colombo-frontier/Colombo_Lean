import GradientHessian.NumericalPostprocessorMeasurability
import GradientHessian.NumericalProductStep
noncomputable section
namespace GradientHessian.NumericalPostExecution
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

open Matrix NumericalPostprocessor

def withConfig
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t)
    (q : Config (t+1) (4096*J^2+1) ell S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
      (Action t (4096*J^2))) : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t :=
  ((s.1.1,s.1.2.1,q),s.2.1,false)

def advance (K : ℝ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) :=
  withConfig t s (NumericalProductStep.fullStep P B fallback t leaf policy K (taskDisclosed leaf j)
    s.1.1.2.1 (cache B t j s) A s.1.2.2)

def next (K : ℝ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) :=
  if halt t leaf j s then s else advance P B fallback t leaf policy K j A s

def macroTime (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
    (E := E) (H := H) (Seed := Seed) (S := S) t) : ℕ :=
  if normalInstruction t s.1.2.2 then 2 else 1

theorem step_advance {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t)
    (hh : halt t leaf j s=false) (hselected : normalInstruction t s.1.2.2=false ∨ s.2.2=true) :
    (program P B fallback t leaf policy hK j).step A s=advance P B fallback t leaf policy K j A s := by
  have hn : (normalInstruction t s.1.2.2 && !s.2.2)=false := by
    rcases hselected with h | h <;> simp [h]
  have hs := NumericalProductStep.one_product_step P B fallback t leaf policy K (taskDisclosed leaf j)
    s.1.1.2.1 (cache B t j s) A s.1.2.2
  cases hp : NumericalDriverInstructions.product leaf (taskDisclosed leaf j) s.1.2.2 with
  | false =>
      simp only [hp,Bool.false_eq_true,if_false] at hs
      simp only [TestSelectionMachine.Program.step,program,mode,hh,hn,hp,Bool.false_eq_true,
        if_false,Fin.isValue,one_ne_zero,if_true,stepReply,advance,withConfig]
      exact congrArg (fun q => ((s.1.1,s.1.2.1,q),s.2.1,false)) hs
  | true =>
      simp only [hp,if_true] at hs
      simp only [TestSelectionMachine.Program.step,program,mode,hh,hn,hp,Bool.false_eq_true,
        if_false,Fin.isValue,reduceCtorEq,if_true,stepReply,query,NumericalPreprocessor.query,advance,withConfig]
      rw [NumericalProductStep.product_coordinates]
      exact congrArg (fun q => ((s.1.1,s.1.2.1,q),s.2.1,false)) hs

theorem step_select {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t)
    (hh : halt t leaf j s=false) (hn : normalInstruction t s.1.2.2=true) (hb : s.2.2=false) :
    (program P B fallback t leaf policy hK j).mode s=3 ∧
      (program P B fallback t leaf policy hK j).step A s=NumericalPostprocessor.selected t s := by
  simp [program,mode,hh,hn,hb,TestSelectionMachine.Program.step]

theorem run_macro {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false) :
    (program P B fallback t leaf policy hK j).run A (macroTime t s) s=
      next P B fallback t leaf policy K j A s := by
  cases hh : halt t leaf j s with
  | true =>
      have hm : (program P B fallback t leaf policy hK j).mode s=0 := by simp [program,mode,hh]
      have hf : (program P B fallback t leaf policy hK j).step A s=s := by
        simp only [TestSelectionMachine.Program.step,hm,if_true]
      simpa only [TestSelectionMachine.Program.run,next,hh,if_true] using
        Function.iterate_fixed hf (macroTime t s)
  | false =>
      cases hn : normalInstruction t s.1.2.2 with
      | false =>
          simpa only [macroTime,hn,Bool.false_eq_true,if_false,TestSelectionMachine.Program.run,
            Function.iterate_one,next,hh] using step_advance P B fallback t leaf policy hK j A s hh (Or.inl hn)
      | true =>
          have hfirst := (step_select P B fallback t leaf policy hK j A s hh hn hb).2
          have hsecond := step_advance P B fallback t leaf policy hK j A (NumericalPostprocessor.selected t s)
            (by simpa only [halt,NumericalPostprocessor.selected] using hh) (Or.inr rfl)
          simp only [macroTime,hn,if_true,TestSelectionMachine.Program.run,Function.iterate_succ_apply',
            Function.iterate_zero,Function.id_def,next,hh,Bool.false_eq_true,if_false]
          rw [hfirst,hsecond]
          rfl

theorem next_flag {K : ℝ} (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false) :
    (next P B fallback t leaf policy K j A s).2.2=false := by
  unfold next
  split_ifs
  · exact hb
  · rfl

end GradientHessian.NumericalPostExecution