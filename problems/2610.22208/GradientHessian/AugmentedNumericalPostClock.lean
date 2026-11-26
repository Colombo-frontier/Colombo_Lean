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
namespace GradientHessian.AugmentedNumericalPostClock
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
def clock (K : ℝ) (cutoff : ℕ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ) : ℕ →
    RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t → ℕ
  | 0,_ => 0
  | N+1,s => clock K cutoff j A N s+macroTime t ((next t P B fallback leaf policy K cutoff j A)^[N] s)

theorem next_iterate_flag (K : ℝ) (cutoff : ℕ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false) (N : ℕ) :
    ((next t P B fallback leaf policy K cutoff j A)^[N] s).2.2=false := by
  induction N with
  | zero => exact hb
  | succ N ih =>
      rw [Function.iterate_succ_apply']
      exact next_flag t P B fallback leaf policy cutoff j A _ ih

theorem run_clock {K : ℝ} (hK : 0<K) (cutoff : ℕ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false) (N : ℕ) :
    (program t P B fallback leaf policy hK cutoff j).run A (clock t P B fallback leaf policy K cutoff j A N s) s=
      (next t P B fallback leaf policy K cutoff j A)^[N] s := by
  induction N with
  | zero => rfl
  | succ N ih =>
      simp only [clock,TestSelectionMachine.Program.run]
      rw [Nat.add_comm (clock t P B fallback leaf policy K cutoff j A N s)
        (macroTime t ((next t P B fallback leaf policy K cutoff j A)^[N] s)),Function.iterate_add_apply]
      change (program t P B fallback leaf policy hK cutoff j).run A
        (macroTime t ((next t P B fallback leaf policy K cutoff j A)^[N] s))
        ((program t P B fallback leaf policy hK cutoff j).run A (clock t P B fallback leaf policy K cutoff j A N s) s)=_
      rw [ih,run_macro t P B fallback leaf policy hK cutoff j A _ (next_iterate_flag t P B fallback leaf policy K cutoff j A s hb N),
        Function.iterate_succ_apply']

theorem clock_bounds (K : ℝ) (cutoff : ℕ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (N : ℕ) :
    N≤clock t P B fallback leaf policy K cutoff j A N s ∧ clock t P B fallback leaf policy K cutoff j A N s≤2*N := by
  induction N with
  | zero => exact ⟨Nat.le_refl _,Nat.le_refl _⟩
  | succ N ih =>
      have hm : 1≤macroTime t ((next t P B fallback leaf policy K cutoff j A)^[N] s) ∧
          macroTime t ((next t P B fallback leaf policy K cutoff j A)^[N] s)≤2 := by
        unfold macroTime
        split_ifs <;> omega
      simp only [clock]
      constructor <;> omega

theorem selected_at_clock {K : ℝ} (hK : 0<K) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false) (N : ℕ)
    (hh : halt t leaf j ((next t P B fallback leaf policy K cutoff j A)^[N] s)=false)
    (hn : normalInstruction t (((next t P B fallback leaf policy K cutoff j A)^[N] s).1.2.2)=true) :
    (program t P B fallback leaf policy hK cutoff j).mode
      ((program t P B fallback leaf policy hK cutoff j).run A (clock t P B fallback leaf policy K cutoff j A N s) s)=3 ∧
    (program t P B fallback leaf policy hK cutoff j).test
      ((program t P B fallback leaf policy hK cutoff j).run A (clock t P B fallback leaf policy K cutoff j A N s) s)=
      BoundedNumericalTest.test (CensoredOracle.numericalMap t (AugmentedNumericalDriver.point t
        (((next t P B fallback leaf policy K cutoff j A)^[N] s).1.2.2))) := by
  rw [run_clock t P B fallback leaf policy hK cutoff j A s hb N]
  exact ⟨(step_select t P B fallback leaf policy hK cutoff j A _ hh hn
    (next_iterate_flag t P B fallback leaf policy K cutoff j A s hb N)).1,rfl⟩

theorem next_cache (K : ℝ) (cutoff : ℕ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) :
    cache t B j (next t P B fallback leaf policy K cutoff j A s)=cache t B j s := by
  unfold next
  split_ifs <;> rfl

theorem iterate_cache (K : ℝ) (cutoff : ℕ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (N : ℕ) :
    cache t B j ((next t P B fallback leaf policy K cutoff j A)^[N] s)=cache t B j s := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply',next_cache,ih]

end GradientHessian.AugmentedNumericalPostClock

