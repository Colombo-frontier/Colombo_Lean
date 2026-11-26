import GradientHessian.NumericalPostCounts
import GradientHessian.NumericalPostDriver
import GradientHessian.ControllerPostWindow
noncomputable section
namespace GradientHessian.NumericalPostBounds
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

open NumericalPostClock NumericalPostCounts NumericalPostDriver ControllerDriverMonotonicity ControllerDriverResource TaskSlots

theorem queryBit_eq_product (j : Fin (4096*J^2+1))
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) :
    queryBit t leaf j s=if NumericalDriverInstructions.product leaf (taskDisclosed leaf j) s.1.2.2 then 1 else 0 := by
  cases hp : NumericalDriverInstructions.product leaf (taskDisclosed leaf j) s.1.2.2 with
  | false => simp [queryBit,hp]
  | true =>
      rcases (NumericalDriverInstructions.product_iff leaf (taskDisclosed leaf j) s.1.2.2).mp hp with
        ⟨n,a,p,before,after,hq,hk,hbefore,hafter,hcur⟩
      have hh : halt t leaf j s=false := by
        simp [halt,hq,NumericalDriverInstructions.finished,stateOf,phaseState,hafter]
      simp [queryBit,hh,hp]

theorem selectionBit_eq_normalBit (j : Fin (4096*J^2+1))
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) :
    selectionBit t leaf j s=normalBit (fun _ => true) (taskDisclosed leaf j) s.1.2.2 := by
  rcases s with ⟨⟨aux,store,q⟩,fresh,b⟩
  cases q with
  | ready n a u => simp [selectionBit,halt,normalInstruction,normalBit,NumericalDriverInstructions.finished]
  | finished a u => simp [selectionBit,halt,normalInstruction,normalBit,NumericalDriverInstructions.finished]
  | pending n a output phase =>
      cases phase with
      | repairing => simp [selectionBit,halt,normalInstruction,normalBit,NumericalDriverInstructions.finished]
      | delivered => simp [selectionBit,halt,normalInstruction,normalBit,NumericalDriverInstructions.finished]
      | frozen => simp [selectionBit,halt,normalInstruction,normalBit,NumericalDriverInstructions.finished]
      | normal p u =>
          cases hk : p.kind <;> cases hs : taskDisclosed leaf j u <;>
            simp [selectionBit,halt,normalInstruction,normalBit,NumericalDriverInstructions.finished,stateOf,phaseState,hk,hs]

theorem macro_counts_bound {K : ℝ} (hK : 0<K) (hell : 0<ell) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false)
    (hq : Ready (stateOf s.1.2.2)) (hcur : TaskState.current (stateOf s.1.2.2)=some leaf)
    (hindex : ((stateOf s.1.2.2).completed leaf).val=j.val) (N : ℕ)
    (hN : halt t leaf j ((next P B fallback t leaf policy K j A)^[N] s)=false) :
    (program P B fallback t leaf policy hK j).queryCount A (clock P B fallback t leaf policy K j A N s) s≤ell+1 ∧
    (program P B fallback t leaf policy hK j).selections A (clock P B fallback t leaf policy K j A N s) s≤ell := by
  have he (i : ℕ) (hi : i≤N) := next_eq_driver P B fallback t leaf policy K j A s hb i
    (next_open_prefix P B fallback t leaf policy K j A s i N hi hN)
  have hqsum : (program P B fallback t leaf policy hK j).queryCount A
      (clock P B fallback t leaf policy K j A N s) s=
      ∑ i∈Finset.range N,if NumericalDriverInstructions.product leaf (taskDisclosed leaf j)
        (driver P B fallback t leaf policy K j A s i) then 1 else 0 := by
    rw [queryCount_clock P B fallback t leaf policy hK j A s hb N]
    apply Finset.sum_congr rfl
    intro i hi
    rw [he i (Nat.le_of_lt (Finset.mem_range.mp hi)),queryBit_eq_product]
    rfl
  have hssum : (program P B fallback t leaf policy hK j).selections A
      (clock P B fallback t leaf policy K j A N s) s=
      ∑ i∈Finset.range N,normalBit (fun _ => true) (taskDisclosed leaf j)
        (driver P B fallback t leaf policy K j A s i) := by
    rw [selections_clock P B fallback t leaf policy hK j A s hb N]
    apply Finset.sum_congr rfl
    intro i hi
    rw [he i (Nat.le_of_lt (Finset.mem_range.mp hi)),selectionBit_eq_normalBit]
    rfl
  rw [hqsum,hssum]
  let R := NumericalShadowRules.shadowRules (ell := ell) P B fallback t leaf K s.1.1.2.1 (cache B t j s)
  let o := NumericalProductStep.ordinary (ell := ell) P B fallback t leaf K s.1.1.2.1 (cache B t j s) A
  let v := NumericalPolicyReplies.rich (ell := ell) P B fallback t leaf K s.1.1.2.1 (cache B t j s)
  have hqp := post_product_bound policy R o v hell leaf j s.1.2.2 hq hcur hindex N
  have hsp := (post_normal_bound policy R o v hell leaf j s.1.2.2 hq hcur hindex N).1
  rw [count_eq_sum] at hsp
  exact ⟨hqp,hsp⟩

theorem capped_selected_endpoint {K : ℝ} (hK : 0<K) (hell : 0<ell) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false)
    (hq : Ready (stateOf s.1.2.2)) (hcur : TaskState.current (stateOf s.1.2.2)=some leaf)
    (hindex : ((stateOf s.1.2.2).completed leaf).val=j.val) (N : ℕ)
    (hN : halt t leaf j ((next P B fallback t leaf policy K j A)^[N] s)=false)
    (hn : normalInstruction t (((next P B fallback t leaf policy K j A)^[N] s).1.2.2)=true) :
    (cappedProgram P B fallback t leaf policy hK j).mode
      ((cappedProgram P B fallback t leaf policy hK j).run A
        (clock P B fallback t leaf policy K j A N s) (s,ell+1,ell+3))=3 ∧
    (cappedProgram P B fallback t leaf policy hK j).test
      ((cappedProgram P B fallback t leaf policy hK j).run A
        (clock P B fallback t leaf policy K j A N s) (s,ell+1,ell+3))=
      BoundedNumericalTest.test (CensoredOracle.numericalMap t (NumericalDriverInstructions.point
        (((next P B fallback t leaf policy K j A)^[N] s).1.2.2))) := by
  have hc := macro_counts_bound P B fallback t leaf policy hK hell j A s hb hq hcur hindex N hN
  have hm := selected_at_clock P B fallback t leaf policy hK j A s hb N hN hn
  have hsel : (program P B fallback t leaf policy hK j).selections A
      (clock P B fallback t leaf policy K j A N s+1) s≤ell+3 := by
    rw [TestSelectionMachine.Program.selections,if_pos hm.1]
    omega
  have he := SelectionCapTransparency.selected_endpoint
    (program P B fallback t leaf policy hK j) A s (ell+1) (ell+3)
    (clock P B fallback t leaf policy K j A N s) hc.1 hsel hm.1
  exact ⟨he.1,he.2.trans hm.2⟩

end GradientHessian.NumericalPostBounds

