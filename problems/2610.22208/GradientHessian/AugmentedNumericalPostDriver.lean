import GradientHessian.AugmentedNumericalPostClock
import GradientHessian.ExternalHaltIteration
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
namespace GradientHessian.AugmentedNumericalPostDriver
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
def driver (K : ℝ) (cutoff : ℕ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ) (s : Run) (N : ℕ) :=
  (AugmentedNumericalExecution.fullCursor P B fallback t leaf policy K cutoff (taskDisclosed leaf j)
    s.1.1.2.2 s.1.1.2.1 (cache t B j s) A)^[N] s.1.2.2

theorem withCursor_self (s : Run) (hb : s.2.2=false) : withCursor t s s.1.2.2=s := by
  rcases s with ⟨⟨aux,store,q⟩,fresh,b⟩
  dsimp only at hb
  cases hb
  rfl

theorem advance_iterate (K : ℝ) (cutoff : ℕ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : Run) (hb : s.2.2=false) (N : ℕ) :
    (advance t P B fallback leaf policy K cutoff j A)^[N] s=
      withCursor t s (driver t P B fallback leaf policy K cutoff j A s N) := by
  induction N with
  | zero => exact (withCursor_self t s hb).symm
  | succ N ih =>
      rw [Function.iterate_succ_apply',ih]
      change withCursor t s (AugmentedNumericalExecution.fullCursor P B fallback t leaf policy K cutoff (taskDisclosed leaf j)
        s.1.1.2.2 s.1.1.2.1 (cache t B j s) A (driver t P B fallback leaf policy K cutoff j A s N))=_
      simp only [driver,Function.iterate_succ_apply']

theorem next_open_prefix (K : ℝ) (cutoff : ℕ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : Run) (i N : ℕ) (hi : i≤N)
    (hN : halt t leaf j ((next t P B fallback leaf policy K cutoff j A)^[N] s)=false) :
    halt t leaf j ((next t P B fallback leaf policy K cutoff j A)^[i] s)=false :=
  ExternalHaltIteration.open_prefix (advance t P B fallback leaf policy K cutoff j A) (halt t leaf j) s i N hi hN

theorem next_eq_driver (K : ℝ) (cutoff : ℕ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : Run) (hb : s.2.2=false) (N : ℕ)
    (hN : halt t leaf j ((next t P B fallback leaf policy K cutoff j A)^[N] s)=false) :
    (next t P B fallback leaf policy K cutoff j A)^[N] s=
      withCursor t s (driver t P B fallback leaf policy K cutoff j A s N) := by
  exact (ExternalHaltIteration.iterate_eq_of_open
    (advance t P B fallback leaf policy K cutoff j A) (halt t leaf j) s N hN).trans
      (advance_iterate t P B fallback leaf policy K cutoff j A s hb N)

theorem driver_endpoint (K : ℝ) (cutoff : ℕ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : Run) (hb : s.2.2=false) (N : ℕ)
    (hpre : ∀ i<N,halt t leaf j (withCursor t s (driver t P B fallback leaf policy K cutoff j A s i))=false) :
    (next t P B fallback leaf policy K cutoff j A)^[N] s=
      withCursor t s (driver t P B fallback leaf policy K cutoff j A s N) := by
  have hh : ∀ i<N,halt t leaf j ((advance t P B fallback leaf policy K cutoff j A)^[i] s)=false := by
    intro i hi
    rw [advance_iterate t P B fallback leaf policy K cutoff j A s hb i]
    exact hpre i hi
  exact (ExternalHaltIteration.iterate_eq_before
    (advance t P B fallback leaf policy K cutoff j A) (halt t leaf j) s N hh).trans
      (advance_iterate t P B fallback leaf policy K cutoff j A s hb N)

end GradientHessian.AugmentedNumericalPostDriver
