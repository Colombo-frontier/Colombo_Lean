import GradientHessian.NumericalPostClock
import GradientHessian.ExternalHaltIteration
import GradientHessian.ControllerPolicyCoupling
noncomputable section
namespace GradientHessian.NumericalPostDriver
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

open NumericalPostClock

def driver (K : ℝ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (N : ℕ) :=
  ControllerPolicyDriver.run policy
    (NumericalShadowRules.shadowRules P B fallback t leaf K s.1.1.2.1 (cache B t j s)) (taskDisclosed leaf j)
    (NumericalProductStep.ordinary P B fallback t leaf K s.1.1.2.1 (cache B t j s) A)
    (NumericalPolicyReplies.rich P B fallback t leaf K s.1.1.2.1 (cache B t j s)) N s.1.2.2

theorem withConfig_self
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false) :
    withConfig t s s.1.2.2=s := by
  rcases s with ⟨⟨aux,store,q⟩,fresh,b⟩
  dsimp only at hb
  cases hb
  rfl

theorem advance_iterate (K : ℝ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false) (N : ℕ) :
    (advance P B fallback t leaf policy K j A)^[N] s=
      withConfig t s (driver P B fallback t leaf policy K j A s N) := by
  induction N with
  | zero => exact (withConfig_self t s hb).symm
  | succ N ih =>
      rw [Function.iterate_succ_apply',ih]
      change withConfig t s (NumericalProductStep.fullStep P B fallback t leaf policy K (taskDisclosed leaf j)
        s.1.1.2.1 (cache B t j s) A (driver P B fallback t leaf policy K j A s N))=_
      simp only [driver,ControllerPolicyCoupling.run_succ_end]
      rfl

theorem next_open_prefix (K : ℝ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (i N : ℕ) (hi : i≤N)
    (hN : halt t leaf j ((next P B fallback t leaf policy K j A)^[N] s)=false) :
    halt t leaf j ((next P B fallback t leaf policy K j A)^[i] s)=false :=
  ExternalHaltIteration.open_prefix (advance P B fallback t leaf policy K j A) (halt t leaf j) s i N hi hN

theorem next_eq_driver (K : ℝ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false) (N : ℕ)
    (hN : halt t leaf j ((next P B fallback t leaf policy K j A)^[N] s)=false) :
    (next P B fallback t leaf policy K j A)^[N] s=
      withConfig t s (driver P B fallback t leaf policy K j A s N) := by
  have he := ExternalHaltIteration.iterate_eq_of_open
    (advance P B fallback t leaf policy K j A) (halt t leaf j) s N hN
  exact he.trans (advance_iterate P B fallback t leaf policy K j A s hb N)

theorem driver_endpoint (K : ℝ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false) (N : ℕ)
    (hpre : ∀ i<N,halt t leaf j (withConfig t s (driver P B fallback t leaf policy K j A s i))=false) :
    (next P B fallback t leaf policy K j A)^[N] s=
      withConfig t s (driver P B fallback t leaf policy K j A s N) := by
  have hh : ∀ i<N,halt t leaf j ((advance P B fallback t leaf policy K j A)^[i] s)=false := by
    intro i hi
    rw [advance_iterate P B fallback t leaf policy K j A s hb i]
    exact hpre i hi
  exact (ExternalHaltIteration.iterate_eq_before
    (advance P B fallback t leaf policy K j A) (halt t leaf j) s N hh).trans
      (advance_iterate P B fallback t leaf policy K j A s hb N)

end GradientHessian.NumericalPostDriver
