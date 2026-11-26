import GradientHessian.AugmentedNumericalPreprocessor
import GradientHessian.AugmentedNumericalSupplyEquality
import GradientHessian.DisclosureIteration

/-! Literal charged preprocessing executes the externally stopped cursor.
The suspended initial cursor remains suspended when the target mark was
supplied initially; otherwise initialization is an uncharged transition. -/

noncomputable section
namespace GradientHessian.AugmentedNumericalPreExecution
open Classical Matrix HigherHierarchy HierarchyAddresses FrontierState TaskState
  NumericalCachedOracle AugmentedNumericalPreprocessor AugmentedNumericalDriver
  AugmentedNumericalExecution AugmentedNumericalSupplyEquality

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (leaf : Leaf (t+1))
variable [MeasurableSpace (DirectionPolicyReplay.Point d J E H t)] [BorelSpace (DirectionPolicyReplay.Point d J E H t)]
  [MeasurableSpace (DirectionPolicyReplay.Ordinary d J E H t)] [BorelSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [MeasurableSpace (DirectionPolicyReplay.Rich d J E H t)] [BorelSpace (DirectionPolicyReplay.Rich d J E H t)]
variable (policy : Machine.Policy (Seed × AugmentedPolicy.Packet d J E H t ell) S
  (DirectionPolicyReplay.Point d J E H t)
  (AugmentedPolicy.Ordinary d J E H t ell) (AugmentedPolicy.Rich d J E H t ell))
local notation "Run" => RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
  (E := E) (H := H) (Seed := Seed) (S := S) t

theorem base_tick {K : ℝ} (hK : 0<K) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ) (s : Run) :
    (baseProgram t P B fallback leaf policy hK cutoff j).tick A readout s=
      (s.1,s.2.1,externalCursor P B fallback t leaf policy K cutoff j
        s.1.2.2 s.1.2.1 (cache t B j s) A s.2.2) := by
  cases hh : halt t leaf j s with
  | true =>
    simp only [DisclosureCompiler.Program.tick,baseProgram,mode,hh,if_true,Fin.isValue]
    change s=(s.1,s.2.1,if halt t leaf j s then s.2.2 else _)
    rw [hh]
    rfl
  | false =>
    have hs := one_product_cursor P B fallback t leaf policy K cutoff (fun _ => false)
      s.1.2.2 s.1.2.1 (cache t B j s) A s.2.2
    cases hp : product t leaf (fun _ => false) s.2.2 with
    | false =>
      simp only [hp,Bool.false_eq_true,if_false] at hs
      simp only [DisclosureCompiler.Program.tick,baseProgram,mode,hh,hp,Bool.false_eq_true,if_false,
        Fin.isValue,one_ne_zero,if_true,stepReply]
      change (s.1,s.2.1,AugmentedNumericalDriver.advance t P B fallback leaf policy K cutoff
        (fun _ => false) s.1.2.2 s.1.2.1 (cache t B j s) 0 s.2.2)=
        (s.1,s.2.1,if halt t leaf j s then s.2.2 else _)
      rw [hh]
      exact congrArg (fun q => (s.1,s.2.1,q)) hs
    | true =>
      simp only [hp,if_true] at hs
      simp only [DisclosureCompiler.Program.tick,baseProgram,mode,hh,hp,Bool.false_eq_true,if_false,
        Fin.isValue,reduceCtorEq,if_true,stepReply,query]
      rw [AugmentedNumericalEquality.product_coordinates]
      change (s.1,s.2.1,AugmentedNumericalDriver.advance t P B fallback leaf policy K cutoff
        (fun _ => false) s.1.2.2 s.1.2.1 (cache t B j s) _ s.2.2)=
        (s.1,s.2.1,if halt t leaf j s then s.2.2 else _)
      rw [hh]
      exact congrArg (fun q => (s.1,s.2.1,q)) hs

theorem base_iterate {K : ℝ} (hK : 0<K) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ) (s : Run) (N : ℕ) :
    ((baseProgram t P B fallback leaf policy hK cutoff j).tick A readout)^[N] s=
      (s.1,s.2.1,(externalCursor P B fallback t leaf policy K cutoff j
        s.1.2.2 s.1.2.1 (cache t B j s) A)^[N] s.2.2) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply',ih,base_tick,Function.iterate_succ_apply']
    rfl

theorem base_eval_state {K : ℝ} (hK : 0<K) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ) (s : Run) (N : ℕ) :
    ((baseProgram t P B fallback leaf policy hK cutoff j).eval A readout N s).2=
      (s.1,s.2.1,(externalCursor P B fallback t leaf policy K cutoff j
        s.1.2.2 s.1.2.1 (cache t B j s) A)^[N] s.2.2) := by
  rw [DisclosureCompiler.Program.eval_state_iterate,base_iterate]

end GradientHessian.AugmentedNumericalPreExecution
