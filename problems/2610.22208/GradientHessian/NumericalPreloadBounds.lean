import GradientHessian.NumericalPreloadExecution
import GradientHessian.ExternalHaltIteration
import GradientHessian.DisclosureCapTransparency
import GradientHessian.NumericalProductStep
import GradientHessian.DisclosureIteration
import GradientHessian.ControllerDriverTaskBounds
noncomputable section
namespace GradientHessian.NumericalPreloadBounds
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

open NumericalPreloadExecution ControllerDriverMonotonicity ControllerDriverResource TaskSlots

def driver (K : ℝ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (N : ℕ) :=
  ControllerPolicyDriver.run policy
    (NumericalShadowRules.shadowRules P B fallback t leaf K s.1.2.1 (cache B t j s)) (fun _ => false)
    (NumericalProductStep.ordinary P B fallback t leaf K s.1.2.1 (cache B t j s) A)
    (NumericalPolicyReplies.rich P B fallback t leaf K s.1.2.1 (cache B t j s)) N s.2.2

theorem driver_iterate (K : ℝ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (N : ℕ) :
    driver P B fallback t leaf policy K j A s N=
      (NumericalProductStep.fullStep P B fallback t leaf policy K (fun _ => false)
        s.1.2.1 (cache B t j s) A)^[N] s.2.2 := by
  generalize hq : s.2.2=q
  dsimp only [driver]
  rw [hq]
  clear hq
  induction N generalizing q with
  | zero => rfl
  | succ N ih =>
      rw [ControllerPolicyDriver.run,Function.iterate_succ_apply]
      exact ih _

theorem base_mode_ne_three {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1))
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) :
    (baseProgram P B fallback t leaf policy hK j).mode s≠3 := by
  simp only [baseProgram]
  split_ifs <;> decide

theorem base_disclosures {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (N : ℕ) :
    (baseProgram P B fallback t leaf policy hK j).disclosures A readout N s=0 := by
  rw [DisclosureCompiler.Program.disclosures_eq_sum]
  apply Finset.sum_eq_zero
  intro i hi
  exact if_neg (base_mode_ne_three P B fallback t leaf policy hK j _)

theorem base_calls_bound {K : ℝ} (hK : 0<K) (hell : 0<ell) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hq : Ready (stateOf s.2.2)) (N : ℕ) :
    (baseProgram P B fallback t leaf policy hK j).ordinaryCalls A readout N s≤(4096*J^2+1)*ell+1 := by
  let f := NumericalProductStep.fullStep (ell := ell) P B fallback t leaf policy K (fun _ => false)
    s.1.2.1 (cache B t j s) A
  let stop := fun q : Config (t+1) (4096*J^2+1) ell S
      (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Action t (4096*J^2)) =>
    NumericalDriverInstructions.finished q || markSupplied leaf j (stateOf q)
  let R := NumericalShadowRules.shadowRules (ell := ell) P B fallback t leaf K s.1.2.1 (cache B t j s)
  let o := NumericalProductStep.ordinary (ell := ell) P B fallback t leaf K s.1.2.1 (cache B t j s) A
  let v := NumericalPolicyReplies.rich (ell := ell) P B fallback t leaf K s.1.2.1 (cache B t j s)
  have hbound := actual_product_bound policy R (fun _ => false) o v hell leaf N s.2.2 hq
  rw [DisclosureCompiler.Program.ordinaryCalls_eq_sum]
  apply le_trans (Finset.sum_le_sum ?_) hbound
  intro i hi
  rw [base_iterate]
  change (if (baseProgram P B fallback t leaf policy hK j).mode
    (s.1,s.2.1,(ExternalHaltIteration.step f stop)^[i] s.2.2)=2 then 1 else 0)≤_
  cases hs : stop ((ExternalHaltIteration.step f stop)^[i] s.2.2) with
  | true =>
      have hm : (baseProgram P B fallback t leaf policy hK j).mode
          (s.1,s.2.1,(ExternalHaltIteration.step f stop)^[i] s.2.2)=0 := by
        change (if stop ((ExternalHaltIteration.step f stop)^[i] s.2.2) then 0 else _)=0
        simp only [hs,if_true]
      simp [hm]
  | false =>
      have he := ExternalHaltIteration.iterate_eq_of_open f stop s.2.2 i hs
      have hd := driver_iterate P B fallback t leaf policy K j A s i
      change driver P B fallback t leaf policy K j A s i=f^[i] s.2.2 at hd
      rw [he,← hd]
      have hh : halt t leaf j (s.1,s.2.1,driver P B fallback t leaf policy K j A s i)=false := by
        change stop (driver P B fallback t leaf policy K j A s i)=false
        rw [hd,← he]
        exact hs
      change (if (baseProgram P B fallback t leaf policy hK j).mode
        (s.1,s.2.1,driver P B fallback t leaf policy K j A s i)=2 then 1 else 0)≤
        if NumericalDriverInstructions.product leaf (fun _ => false)
          (driver P B fallback t leaf policy K j A s i) then 1 else 0
      cases hp : NumericalDriverInstructions.product leaf (fun _ => false)
        (driver P B fallback t leaf policy K j A s i) <;> simp [baseProgram,hh,hp]

theorem preload_calls_bound {K : ℝ} (hK : 0<K) (hell : 0<ell) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hq : Ready (stateOf s.2.2)) (N : ℕ) :
    (NumericalPreloadRuntime.program P B fallback t leaf policy hK j).ordinaryCalls A readout (j.val+N) (s,j.val)
        ≤(4096*J^2+1)*ell+1 ∧
    (NumericalPreloadRuntime.program P B fallback t leaf policy hK j).disclosures A readout (j.val+N) (s,j.val)=j.val := by
  have hc := DisclosurePreload.calls_prepared (baseProgram P B fallback t leaf policy hK j)
    (mark B t j) (write t) (mark_measurable B t j) (write_measurable t) A readout j.val N s
  rw [prepared_exact B t j readout j.val (Nat.le_of_lt j.isLt)] at hc
  change (NumericalPreloadRuntime.program P B fallback t leaf policy hK j).ordinaryCalls A readout (j.val+N) (s,j.val)=_ ∧
    (NumericalPreloadRuntime.program P B fallback t leaf policy hK j).disclosures A readout (j.val+N) (s,j.val)=_ at hc
  constructor
  · rw [hc.1]
    exact base_calls_bound P B fallback t leaf policy hK hell j A readout (filled B t j readout j.val s) hq N
  · rw [hc.2,base_disclosures]
    exact Nat.zero_add _

theorem capped_preload_projects {K : ℝ} (hK : 0<K) (hell : 0<ell) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hq : Ready (stateOf s.2.2)) (N : ℕ) :
    ((DisclosureCappedProgram.cap (NumericalPreloadRuntime.program P B fallback t leaf policy hK j)).eval A readout
      (j.val+N) ((s,j.val),(4096*J^2+1)*ell+1,4096*J^2+1)).2.1=
      ((NumericalPreloadRuntime.program P B fallback t leaf policy hK j).eval A readout (j.val+N) (s,j.val)).2 := by
  have hc := preload_calls_bound P B fallback t leaf policy hK hell j A readout s hq N
  apply DisclosureCappedProgram.eval_projects _ A readout (j.val+N) (s,j.val) _ _ hc.1
  rw [hc.2]
  exact Nat.le_of_lt j.isLt

theorem capped_preload_halted {K : ℝ} (hK : 0<K) (hell : 0<ell) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hq : Ready (stateOf s.2.2)) (N : ℕ)
    (hh : ((NumericalPreloadRuntime.program P B fallback t leaf policy hK j).eval A readout (j.val+N) (s,j.val)).1=true) :
    ((DisclosureCappedProgram.cap (NumericalPreloadRuntime.program P B fallback t leaf policy hK j)).eval A readout
      (j.val+N) ((s,j.val),(4096*J^2+1)*ell+1,4096*J^2+1)).1=true := by
  have hc := preload_calls_bound P B fallback t leaf policy hK hell j A readout s hq N
  apply DisclosureCappedProgram.eval_halted _ A readout (j.val+N) (s,j.val) _ _ hc.1 _ hh
  rw [hc.2]
  exact Nat.le_of_lt j.isLt

end GradientHessian.NumericalPreloadBounds

