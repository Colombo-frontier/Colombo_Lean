import GradientHessian.NumericalPreloadRuntime
import GradientHessian.NumericalProductStep
import GradientHessian.DisclosureIteration
import GradientHessian.ControllerDriverTaskBounds
noncomputable section
namespace GradientHessian.NumericalPreloadExecution
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

open Matrix NumericalPreprocessor NumericalPreloadRuntime

def externalStep (K : ℝ) (j : Fin (4096*J^2+1))
    (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J) (A : Matrix (Fin d) (Fin d) ℝ)
    (q : Config (t+1) (4096*J^2+1) ell S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
      (Action t (4096*J^2))) :=
  if NumericalDriverInstructions.finished q || markSupplied leaf j (ControllerDriverMonotonicity.stateOf q) then q
  else NumericalProductStep.fullStep P B fallback t leaf policy K (fun _ => false) w c A q

theorem base_tick {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) :
    (baseProgram P B fallback t leaf policy hK j).tick A readout s=
      (s.1,s.2.1,externalStep P B fallback t leaf policy K j s.1.2.1 (cache B t j s) A s.2.2) := by
  cases hh : halt t leaf j s with
  | true =>
      simp only [DisclosureCompiler.Program.tick,baseProgram,NumericalPreprocessor.program,hh,
        if_true,Fin.isValue]
      change s=(s.1,s.2.1,if halt t leaf j s then s.2.2 else _)
      rw [hh]
      rfl
  | false =>
      have hs := NumericalProductStep.one_product_step P B fallback t leaf policy K (fun _ => false)
        s.1.2.1 (cache B t j s) A s.2.2
      cases hp : NumericalDriverInstructions.product leaf (fun _ => false) s.2.2 with
      | false =>
          simp only [hp,Bool.false_eq_true,if_false] at hs
          simp only [DisclosureCompiler.Program.tick,baseProgram,NumericalPreprocessor.program,hh,hp,
            Bool.false_eq_true,if_false,Fin.isValue,one_ne_zero,if_true,unfrozenReply]
          change (s.1,s.2.1,NumericalRuntime.advance _ _ _ _ _ _ _ _ _ _ 0 s.2.2)=
            (s.1,s.2.1,if halt t leaf j s then s.2.2 else _)
          rw [hh]
          exact congrArg (fun q => (s.1,s.2.1,q)) hs
      | true =>
          simp only [hp,if_true] at hs
          simp only [DisclosureCompiler.Program.tick,baseProgram,NumericalPreprocessor.program,hh,hp,
            Bool.false_eq_true,if_false,Fin.isValue,reduceCtorEq,if_true,unfrozenReply,query]
          rw [NumericalProductStep.product_coordinates]
          change (s.1,s.2.1,NumericalRuntime.advance _ _ _ _ _ _ _ _ _ _ _ s.2.2)=
            (s.1,s.2.1,if halt t leaf j s then s.2.2 else _)
          rw [hh]
          exact congrArg (fun q => (s.1,s.2.1,q)) hs

theorem base_iterate {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (N : ℕ) :
    ((baseProgram P B fallback t leaf policy hK j).tick A readout)^[N] s=
      (s.1,s.2.1,(externalStep P B fallback t leaf policy K j s.1.2.1 (cache B t j s) A)^[N] s.2.2) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [Function.iterate_succ_apply',ih,base_tick,Function.iterate_succ_apply']
      rfl

theorem base_eval_state {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (N : ℕ) :
    ((baseProgram P B fallback t leaf policy hK j).eval A readout N s).2=
      (s.1,s.2.1,(externalStep P B fallback t leaf policy K j s.1.2.1 (cache B t j s) A)^[N] s.2.2) := by
  rw [DisclosureCompiler.Program.eval_state_iterate,base_iterate]

end GradientHessian.NumericalPreloadExecution
