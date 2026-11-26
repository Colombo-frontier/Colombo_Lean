import GradientHessian.AugmentedNumericalPostCounts
import GradientHessian.AugmentedNumericalPostDriver
import GradientHessian.ControllerPostWindow
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
namespace GradientHessian.AugmentedNumericalPostBounds
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
open AugmentedNumericalPostCounts AugmentedNumericalPostDriver ControllerDriverMonotonicity TaskSlots ControllerPolicyDriver

theorem queryBit_eq_product (j : Fin (4096*J^2+1)) (s : Run) :
    queryBit t leaf j s=if AugmentedNumericalDriver.product t leaf (taskDisclosed leaf j) s.1.2.2 then 1 else 0 := by
  cases hp : AugmentedNumericalDriver.product t leaf (taskDisclosed leaf j) s.1.2.2 with
  | false => simp [queryBit,hp]
  | true =>
      rcases s with ⟨⟨aux,store,q⟩,fresh,b⟩
      cases q with
      | inl star => cases hp
      | inr q =>
          rcases (NumericalDriverInstructions.product_iff leaf (taskDisclosed leaf j) q).mp hp with
            ⟨n,a,p,before,after,hq,hk,hbefore,hafter,hcur⟩
          have hh : halt t leaf j ((aux,store,Sum.inr q),fresh,b)=false := by
            simp [halt,AugmentedNumericalDriver.finished,AugmentedNumericalDriver.state,
              hq,NumericalDriverInstructions.finished,ControllerDriverMonotonicity.stateOf,
              ControllerDriverMonotonicity.phaseState,hafter]
          simpa [queryBit,hp] using hh

theorem selectionBit_eq_normal (j : Fin (4096*J^2+1)) (s : Run) :
    selectionBit t leaf j s=if normalInstruction t s.1.2.2 &&
      !taskDisclosed leaf j (AugmentedNumericalDriver.state t s.1.2.2) then 1 else 0 := by
  rcases s with ⟨⟨aux,store,q⟩,fresh,b⟩
  cases q with
  | inl star => simp [selectionBit,halt,normalInstruction]
  | inr q =>
      cases q with
      | ready n a u => simp [selectionBit,halt,normalInstruction,NumericalPostprocessor.normalInstruction]
      | finished a u => simp [selectionBit,halt,normalInstruction,NumericalPostprocessor.normalInstruction]
      | pending n a output phase =>
          cases phase with
          | repairing => simp [selectionBit,halt,normalInstruction,NumericalPostprocessor.normalInstruction]
          | delivered => simp [selectionBit,halt,normalInstruction,NumericalPostprocessor.normalInstruction]
          | frozen => simp [selectionBit,halt,normalInstruction,NumericalPostprocessor.normalInstruction]
          | normal p u =>
              cases hk : p.kind <;> cases hs : taskDisclosed leaf j u <;>
                simp [selectionBit,halt,normalInstruction,NumericalPostprocessor.normalInstruction,
                  AugmentedNumericalDriver.finished,AugmentedNumericalDriver.state,
                  NumericalDriverInstructions.finished,stateOf,phaseState,hk,hs]

theorem macro_counts_bound {K : ℝ} (hK : 0<K) (hell : 0<ell) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false)
    (hq : Ready (AugmentedNumericalDriver.state t s.1.2.2)) (hcur : TaskState.current (AugmentedNumericalDriver.state t s.1.2.2)=some leaf)
    (hindex : ((AugmentedNumericalDriver.state t s.1.2.2).completed leaf).val=j.val) (N : ℕ)
    (hN : halt t leaf j ((next t P B fallback leaf policy K cutoff j A)^[N] s)=false) :
    (program t P B fallback leaf policy hK cutoff j).queryCount A (clock t P B fallback leaf policy K cutoff j A N s) s≤ell+1 ∧
    (program t P B fallback leaf policy hK cutoff j).selections A (clock t P B fallback leaf policy K cutoff j A N s) s≤ell := by
  have he (i : ℕ) (hi : i≤N) := next_eq_driver t P B fallback leaf policy K cutoff j A s hb i
    (next_open_prefix t P B fallback leaf policy K cutoff j A s i N hi hN)
  have hqsum : (program t P B fallback leaf policy hK cutoff j).queryCount A
      (clock t P B fallback leaf policy K cutoff j A N s) s=
      ∑ i∈Finset.range N,if AugmentedNumericalDriver.product t leaf (taskDisclosed leaf j)
        (driver t P B fallback leaf policy K cutoff j A s i) then 1 else 0 := by
    rw [queryCount_clock t P B fallback leaf policy hK cutoff j A s hb N]
    apply Finset.sum_congr rfl
    intro i hi
    rw [he i (Nat.le_of_lt (Finset.mem_range.mp hi)),queryBit_eq_product]
    rfl
  have hssum : (program t P B fallback leaf policy hK cutoff j).selections A
      (clock t P B fallback leaf policy K cutoff j A N s) s=
      ∑ i∈Finset.range N,if normalInstruction t (driver t P B fallback leaf policy K cutoff j A s i) &&
        !taskDisclosed leaf j (AugmentedNumericalDriver.state t (driver t P B fallback leaf policy K cutoff j A s i)) then 1 else 0 := by
    rw [selections_clock t P B fallback leaf policy hK cutoff j A s hb N]
    apply Finset.sum_congr rfl
    intro i hi
    rw [he i (Nat.le_of_lt (Finset.mem_range.mp hi)),selectionBit_eq_normal]
    rfl
  rw [hqsum,hssum]
  exact ⟨AugmentedNumericalExecution.post_product_bound P B fallback t leaf policy K cutoff j
    s.1.1.2.2 s.1.1.2.1 (cache t B j s) A hell N s.1.2.2 hq hcur hindex,
    AugmentedNumericalExecution.post_normal_bound P B fallback t leaf policy K cutoff j
    s.1.1.2.2 s.1.1.2.1 (cache t B j s) A hell N s.1.2.2 hq hcur hindex⟩

theorem capped_selected_endpoint {K : ℝ} (hK : 0<K) (hell : 0<ell) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false)
    (hq : Ready (AugmentedNumericalDriver.state t s.1.2.2)) (hcur : TaskState.current (AugmentedNumericalDriver.state t s.1.2.2)=some leaf)
    (hindex : ((AugmentedNumericalDriver.state t s.1.2.2).completed leaf).val=j.val) (N : ℕ)
    (hN : halt t leaf j ((next t P B fallback leaf policy K cutoff j A)^[N] s)=false)
    (hn : normalInstruction t (((next t P B fallback leaf policy K cutoff j A)^[N] s).1.2.2)=true) :
    (cappedProgram t P B fallback leaf policy hK cutoff j).mode
      ((cappedProgram t P B fallback leaf policy hK cutoff j).run A
        (clock t P B fallback leaf policy K cutoff j A N s) (s,ell+1,ell+3))=3 ∧
    (cappedProgram t P B fallback leaf policy hK cutoff j).test
      ((cappedProgram t P B fallback leaf policy hK cutoff j).run A
        (clock t P B fallback leaf policy K cutoff j A N s) (s,ell+1,ell+3))=
      BoundedNumericalTest.test (CensoredOracle.numericalMap t (AugmentedNumericalDriver.point t
        (((next t P B fallback leaf policy K cutoff j A)^[N] s).1.2.2))) := by
  have hc := macro_counts_bound t P B fallback leaf policy hK hell cutoff j A s hb hq hcur hindex N hN
  have hm := selected_at_clock t P B fallback leaf policy hK cutoff j A s hb N hN hn
  have hsel : (program t P B fallback leaf policy hK cutoff j).selections A
      (clock t P B fallback leaf policy K cutoff j A N s+1) s≤ell+3 := by
    rw [TestSelectionMachine.Program.selections,if_pos hm.1]
    omega
  have he := SelectionCapTransparency.selected_endpoint
    (program t P B fallback leaf policy hK cutoff j) A s (ell+1) (ell+3)
    (clock t P B fallback leaf policy K cutoff j A N s) hc.1 hsel hm.1
  exact ⟨he.1,he.2.trans hm.2⟩

end GradientHessian.AugmentedNumericalPostBounds

