import GradientHessian.NumericalPostExecution
noncomputable section
namespace GradientHessian.NumericalPostClock
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

def clock (K : ℝ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ) : ℕ →
    RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t → ℕ
  | 0,_ => 0
  | N+1,s => clock K j A N s+macroTime t ((next P B fallback t leaf policy K j A)^[N] s)

theorem next_iterate_flag (K : ℝ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false) (N : ℕ) :
    ((next P B fallback t leaf policy K j A)^[N] s).2.2=false := by
  induction N with
  | zero => exact hb
  | succ N ih =>
      rw [Function.iterate_succ_apply']
      exact next_flag P B fallback t leaf policy j A _ ih

theorem run_clock {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false) (N : ℕ) :
    (program P B fallback t leaf policy hK j).run A (clock P B fallback t leaf policy K j A N s) s=
      (next P B fallback t leaf policy K j A)^[N] s := by
  induction N with
  | zero => rfl
  | succ N ih =>
      simp only [clock,TestSelectionMachine.Program.run]
      rw [Nat.add_comm (clock P B fallback t leaf policy K j A N s)
        (macroTime t ((next P B fallback t leaf policy K j A)^[N] s)),Function.iterate_add_apply]
      change (program P B fallback t leaf policy hK j).run A
        (macroTime t ((next P B fallback t leaf policy K j A)^[N] s))
        ((program P B fallback t leaf policy hK j).run A (clock P B fallback t leaf policy K j A N s) s)=_
      rw [ih,run_macro P B fallback t leaf policy hK j A _ (next_iterate_flag P B fallback t leaf policy K j A s hb N),
        Function.iterate_succ_apply']

theorem clock_bounds (K : ℝ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (N : ℕ) :
    N≤clock P B fallback t leaf policy K j A N s ∧ clock P B fallback t leaf policy K j A N s≤2*N := by
  induction N with
  | zero => exact ⟨Nat.le_refl _,Nat.le_refl _⟩
  | succ N ih =>
      have hm : 1≤macroTime t ((next P B fallback t leaf policy K j A)^[N] s) ∧
          macroTime t ((next P B fallback t leaf policy K j A)^[N] s)≤2 := by
        unfold macroTime
        split_ifs <;> omega
      simp only [clock]
      constructor <;> omega

theorem selected_at_clock {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false) (N : ℕ)
    (hh : halt t leaf j ((next P B fallback t leaf policy K j A)^[N] s)=false)
    (hn : normalInstruction t (((next P B fallback t leaf policy K j A)^[N] s).1.2.2)=true) :
    (program P B fallback t leaf policy hK j).mode
      ((program P B fallback t leaf policy hK j).run A (clock P B fallback t leaf policy K j A N s) s)=3 ∧
    (program P B fallback t leaf policy hK j).test
      ((program P B fallback t leaf policy hK j).run A (clock P B fallback t leaf policy K j A N s) s)=
      BoundedNumericalTest.test (CensoredOracle.numericalMap t (NumericalDriverInstructions.point
        (((next P B fallback t leaf policy K j A)^[N] s).1.2.2))) := by
  rw [run_clock P B fallback t leaf policy hK j A s hb N]
  exact ⟨(step_select P B fallback t leaf policy hK j A _ hh hn
    (next_iterate_flag P B fallback t leaf policy K j A s hb N)).1,rfl⟩

theorem next_cache (K : ℝ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) :
    cache B t j (next P B fallback t leaf policy K j A s)=cache B t j s := by
  unfold next
  split_ifs <;> rfl

theorem iterate_cache (K : ℝ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (N : ℕ) :
    cache B t j ((next P B fallback t leaf policy K j A)^[N] s)=cache B t j s := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply',next_cache,ih]

end GradientHessian.NumericalPostClock
