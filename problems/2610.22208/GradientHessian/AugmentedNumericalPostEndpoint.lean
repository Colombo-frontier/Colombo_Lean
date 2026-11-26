import GradientHessian.AugmentedNumericalPostBounds
import GradientHessian.AugmentedNumericalCursorOpen
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
namespace GradientHessian.AugmentedNumericalPostEndpoint
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
open AugmentedNumericalPostCounts AugmentedNumericalPostDriver ControllerDriverMonotonicity TaskSlots

open AugmentedNumericalPostBounds VisibilityTaskWindow ControllerPolicyDriver ComparisonController

def unguarded (K : ℝ) (cutoff : ℕ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : Run) (N : ℕ) :=
  (AugmentedNumericalExecution.fullCursor P B fallback t leaf policy K cutoff (fun _ => false)
    s.1.1.2.2 s.1.1.2.1 (cache t B j s) A)^[N] s.1.2.2

theorem selected_of_unguarded_normal {K : ℝ} (hK : 0<K) (hell : 0<ell) (cutoff : ℕ)
    (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : Run) (hb : s.2.2=false)
    (hq : Ready (AugmentedNumericalDriver.state t s.1.2.2))
    (hc : AugmentedNumericalCursorInvariant.coherent (taskDisclosed leaf j) s.1.2.2)
    (hcur : TaskState.current (AugmentedNumericalDriver.state t s.1.2.2)=some leaf)
    (hindex : ((AugmentedNumericalDriver.state t s.1.2.2).completed leaf).val=j.val)
    (N rem : ℕ) (a : S) (output : Bool)
    (p : Pending (DirectionPolicyReplay.Point d J E H t))
    (u : State (t+1) (4096*J^2+1) ell)
    (he : unguarded t P B fallback leaf policy K cutoff j A s N=Sum.inr (.pending rem a output (.normal p u)))
    (hk : p.kind=.ordinary) (hs : taskDisclosed leaf j u=false) :
    ∃ fuel,(cappedProgram t P B fallback leaf policy hK cutoff j).mode
        ((cappedProgram t P B fallback leaf policy hK cutoff j).run A fuel (s,ell+1,ell+3))=3 ∧
      (cappedProgram t P B fallback leaf policy hK cutoff j).test
        ((cappedProgram t P B fallback leaf policy hK cutoff j).run A fuel (s,ell+1,ell+3))=
          BoundedNumericalTest.test (CensoredOracle.numericalMap t p.point) := by
  let R := NumericalShadowRules.shadowRules (ell := ell) P B fallback t leaf K s.1.1.2.1 (cache t B j s)
  let o := AugmentedNumericalEquality.ordinary (ell := ell) P B fallback t leaf K s.1.1.2.1 (cache t B j s) A
  let v := AugmentedNumericalReplies.rich (ell := ell) P B fallback t leaf K s.1.1.2.1 (cache t B j s)
  let initial := AugmentedNumericalDriver.startConfig t P B fallback leaf policy K cutoff
    s.1.1.2.2 s.1.1.2.1 (cache t B j s)
  have hi : Coherent (taskDisclosed leaf j) initial := by
    exact TaskSlots.initial_ready hell
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
  have hend : taskDisclosed leaf j (AugmentedNumericalCursorCounts.state initial
      (AugmentedNumericalCursorCounts.run policy R (fun _ => false) o v initial N s.1.2.2))=false := by
    change taskDisclosed leaf j (AugmentedNumericalCursorCounts.state initial
      (unguarded t P B fallback leaf policy K cutoff j A s N))=false
    rw [he]
    exact hs
  have hopen (i : ℕ) (hii : i≤N) := AugmentedNumericalCursorInvariant.open_prefix
    policy R o v initial (taskDisclosed leaf j) hell hr hn hi N i hii s.1.2.2 hc hend
  have hguard (i : ℕ) (hii : i≤N) : driver t P B fallback leaf policy K cutoff j A s i=
      unguarded t P B fallback leaf policy K cutoff j A s i :=
    AugmentedNumericalCursorInvariant.guarded_eq_of_open_endpoint
      policy R o v initial (taskDisclosed leaf j) hell hr hn hi i s.1.2.2 hc (hopen i hii)
  have hf : AugmentedNumericalCursorInvariant.finished
      (AugmentedNumericalCursorCounts.run policy R (fun _ => false) o v initial N s.1.2.2)=false := by
    change AugmentedNumericalCursorInvariant.finished (unguarded t P B fallback leaf policy K cutoff j A s N)=false
    rw [he]
    rfl
  have hpre (i : ℕ) (hii : i≤N) :
      halt t leaf j (withCursor t s (driver t P B fallback leaf policy K cutoff j A s i))=false := by
    rw [hguard i hii]
    have hfi := AugmentedNumericalCursorInvariant.unfinished_prefix policy R o v initial N i hii s.1.2.2 hf
    have hsi := hopen i hii
    rw [AugmentedNumericalExecution.cursor_state P B fallback t leaf policy K cutoff
      s.1.1.2.2 s.1.1.2.1 (cache t B j s)] at hsi
    change (AugmentedNumericalDriver.finished t (unguarded t P B fallback leaf policy K cutoff j A s i) ||
      taskDisclosed leaf j (AugmentedNumericalDriver.state t (unguarded t P B fallback leaf policy K cutoff j A s i)))=false
    have hfinished : AugmentedNumericalDriver.finished t (unguarded t P B fallback leaf policy K cutoff j A s i)=false := by
      change AugmentedNumericalCursorInvariant.finished (unguarded t P B fallback leaf policy K cutoff j A s i)=false at hfi
      have heq : AugmentedNumericalCursorInvariant.finished (unguarded t P B fallback leaf policy K cutoff j A s i)=
          AugmentedNumericalDriver.finished t (unguarded t P B fallback leaf policy K cutoff j A s i) := by
        cases unguarded t P B fallback leaf policy K cutoff j A s i <;> rfl
      exact heq.symm.trans hfi
    rw [hfinished,show taskDisclosed leaf j (AugmentedNumericalDriver.state t
      (unguarded t P B fallback leaf policy K cutoff j A s i))=false from hsi]
    rfl
  have hnext := driver_endpoint t P B fallback leaf policy K cutoff j A s hb N (fun i hii => hpre i hii.le)
  have hN : halt t leaf j ((next t P B fallback leaf policy K cutoff j A)^[N] s)=false := by
    rw [hnext]
    exact hpre N le_rfl
  have hnormal : normalInstruction t (((next t P B fallback leaf policy K cutoff j A)^[N] s).1.2.2)=true := by
    rw [hnext,hguard N le_rfl,he]
    simp [withCursor,normalInstruction,NumericalPostprocessor.normalInstruction,hk]
  have hh := capped_selected_endpoint t P B fallback leaf policy hK hell cutoff j A s hb hq hcur hindex N hN hnormal
  refine ⟨clock t P B fallback leaf policy K cutoff j A N s,hh.1,?_⟩
  rw [hh.2,hnext,hguard N le_rfl,he]
  rfl

end GradientHessian.AugmentedNumericalPostEndpoint
