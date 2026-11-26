import GradientHessian.NumericalPostBounds
import GradientHessian.NumericalSupplySplit
import GradientHessian.NumericalPostDriver
import GradientHessian.ControllerPostWindow
noncomputable section
namespace GradientHessian.NumericalPostEndpoint
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

open NumericalPostBounds VisibilityTaskWindow

def unguarded (K : ℝ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (N : ℕ) :=
  ControllerPolicyDriver.run policy
    (NumericalShadowRules.shadowRules P B fallback t leaf K s.1.1.2.1 (cache B t j s)) (fun _ => false)
    (NumericalProductStep.ordinary P B fallback t leaf K s.1.1.2.1 (cache B t j s) A)
    (NumericalPolicyReplies.rich P B fallback t leaf K s.1.1.2.1 (cache B t j s)) N s.1.2.2

theorem selected_of_unguarded_normal {K : ℝ} (hK : 0<K) (hell : 0<ell) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) (hb : s.2.2=false)
    (hq : Ready (stateOf s.1.2.2)) (hc : Coherent (taskDisclosed leaf j) s.1.2.2)
    (hcur : TaskState.current (stateOf s.1.2.2)=some leaf)
    (hindex : ((stateOf s.1.2.2).completed leaf).val=j.val) (N rem : ℕ) (a : S) (output : Bool)
    (p : Pending (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t))
    (u : State (t+1) (4096*J^2+1) ell)
    (he : unguarded P B fallback t leaf policy K j A s N=.pending rem a output (.normal p u))
    (hk : p.kind=.ordinary) (hs : taskDisclosed leaf j u=false) :
    ∃ fuel,(cappedProgram P B fallback t leaf policy hK j).mode
        ((cappedProgram P B fallback t leaf policy hK j).run A fuel (s,ell+1,ell+3))=3 ∧
      (cappedProgram P B fallback t leaf policy hK j).test
        ((cappedProgram P B fallback t leaf policy hK j).run A fuel (s,ell+1,ell+3))=
          BoundedNumericalTest.test (CensoredOracle.numericalMap t p.point) := by
  let R := NumericalShadowRules.shadowRules (ell := ell) P B fallback t leaf K s.1.1.2.1 (cache B t j s)
  let o := NumericalProductStep.ordinary (ell := ell) P B fallback t leaf K s.1.1.2.1 (cache B t j s) A
  let v := NumericalPolicyReplies.rich (ell := ell) P B fallback t leaf K s.1.1.2.1 (cache B t j s)
  have hr : ∀ w : State (t+1) (4096*J^2+1) ell,Ready w → ∀ b,
      taskDisclosed leaf j w=true → taskDisclosed leaf j (retireNode w (R.target b))=true := by
    intro w _ b hw
    apply decide_eq_true
    exact (of_decide_eq_true hw).trans_le (retireSet_completed_mono w _ leaf)
  have hn : ∀ w : State (t+1) (4096*J^2+1) ell,Ready w → ∀ p',
      taskDisclosed leaf j w=true → taskDisclosed leaf j (normal R p' w)=true := by
    intro w hw p' hs'
    apply decide_eq_true
    exact (of_decide_eq_true hs').trans_le (normal_completed_mono R p' hw leaf)
  have hend : taskDisclosed leaf j (stateOf (ControllerPolicyDriver.run policy R (fun _ => false) o v N s.1.2.2))=false := by
    change taskDisclosed leaf j (stateOf (unguarded P B fallback t leaf policy K j A s N))=false
    rw [he]
    exact hs
  have hopen (i : ℕ) (hi : i≤N) :
      taskDisclosed leaf j (stateOf (ControllerPolicyDriver.run policy R (fun _ => false) o v i s.1.2.2))=false := by
    cases hstop : taskDisclosed leaf j (stateOf (ControllerPolicyDriver.run policy R (fun _ => false) o v i s.1.2.2)) with
    | false => rfl
    | true =>
        have hco := run_coherent policy R (taskDisclosed leaf j) o v hell hn s.1.2.2 hc i
        have hh := stop_persists_run policy R (taskDisclosed leaf j) o v hell hr hn _ hco hstop (N-i)
        rw [← ControllerPolicyDriver.run_add,Nat.add_sub_of_le hi,hend] at hh
        cases hh
  have hguard (i : ℕ) (hi : i≤N) : driver P B fallback t leaf policy K j A s i=
      unguarded P B fallback t leaf policy K j A s i :=
    guarded_eq_at_open_endpoint policy R (taskDisclosed leaf j) o v hell hr hn s.1.2.2 hc i (hopen i hi)
  have hf : NumericalDriverInstructions.finished (ControllerPolicyDriver.run policy R (fun _ => false) o v N s.1.2.2)=false := by
    change NumericalDriverInstructions.finished (unguarded P B fallback t leaf policy K j A s N)=false
    rw [he]
    rfl
  have hpre (i : ℕ) (hi : i≤N) :
      halt t leaf j (withConfig t s (driver P B fallback t leaf policy K j A s i))=false := by
    rw [hguard i hi]
    have hfi := NumericalSupplySplit.unfinished_prefix policy R o v s.1.2.2 N i hi hf
    change (NumericalDriverInstructions.finished (unguarded P B fallback t leaf policy K j A s i) ||
      taskDisclosed leaf j (stateOf (unguarded P B fallback t leaf policy K j A s i)))=false
    rw [show NumericalDriverInstructions.finished (unguarded P B fallback t leaf policy K j A s i)=false from hfi,
      show taskDisclosed leaf j (stateOf (unguarded P B fallback t leaf policy K j A s i))=false from hopen i hi]
    rfl
  have hnext := driver_endpoint P B fallback t leaf policy K j A s hb N (fun i hi => hpre i hi.le)
  have hN : halt t leaf j ((next P B fallback t leaf policy K j A)^[N] s)=false := by
    rw [hnext]
    exact hpre N le_rfl
  have hnormal : normalInstruction t (((next P B fallback t leaf policy K j A)^[N] s).1.2.2)=true := by
    rw [hnext,hguard N le_rfl,he]
    simp [withConfig,normalInstruction,hk]
  have hh := capped_selected_endpoint P B fallback t leaf policy hK hell j A s hb hq hcur hindex N hN hnormal
  refine ⟨clock P B fallback t leaf policy K j A N s,hh.1,?_⟩
  rw [hh.2,hnext,hguard N le_rfl,he]
  rfl

end GradientHessian.NumericalPostEndpoint
