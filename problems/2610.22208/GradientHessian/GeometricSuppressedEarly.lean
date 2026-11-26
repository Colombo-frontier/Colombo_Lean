import GradientHessian.GeometricStoppedEarly
import GradientHessian.ControllerOpenSuppression
import GradientHessian.NumericalShadowRules

/-! Suppressing every future-mark test of a fixed leaf preserves every
actual early completion at that leaf. Any chosen suppressed action would
retire that leaf permanently, contradicting the open endpoint. -/

noncomputable section
namespace GradientHessian.GeometricSuppressedEarly
universe u
open Classical HigherHierarchy HierarchyParameters CensoredOracle ControllerCensor
  FrontierState TaskState TaskSlots ComparisonController GeometricRepair JetLocality
  CensoredPolicy ControllerPolicyDriver ControllerNormalRealization GeometricDisclosure
  ComparisonControllerReplay ControllerDriverMonotonicity VisibilityWindow VisibilityTaskWindow
  NumericalShadowRules

theorem blocked_retires_target {t m ell : ℕ} (leaf : Leaf (t+1)) (j : Fin (m+1))
    (s : State (t+1) (m+1) ell) (a : Action t m) (ha : blockLeaf leaf a=true) :
    taskDisclosed leaf j (retireNode s (target a))=true := by
  cases a with
  | localized h path i => simp [blockLeaf] at ha
  | old path i k => simp [blockLeaf] at ha
  | inner q k l => simp [blockLeaf] at ha
  | futureMark q k =>
    have hq : q=leaf := of_decide_eq_true ha
    subst q
    simp [taskDisclosed,target,retireNode,retireSet,j.isLt]

variable {Y E : Type u} {H : ℕ → Type u} {m ell : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (t : ℕ)
variable [MeasurableSpace (Space Y E H m t)]
  [MeasurableSpace (ℝ × (Space Y E H m t →L[ℝ] ℝ))]
  [MeasurableSpace (ℝ × (Space Y E H m t →L[ℝ] ℝ) ×
    (Space Y E H m t →L[ℝ] Space Y E H m t →L[ℝ] ℝ))]
variable (P : Machine.Policy Seed S (Space Y E H m t)
  (ℝ × (Space Y E H m t →L[ℝ] ℝ))
  (ℝ × (Space Y E H m t →L[ℝ] ℝ) × (Space Y E H m t →L[ℝ] Space Y E H m t →L[ℝ] ℝ)))

theorem original_early_has_suppressed_normal_phase {K : ℝ} (hK : 0<K) (θ : Parameters Y E H m t)
    (hd : Valid Y E H m t (decode t θ)) (hell : 0<ell) (N : ℕ) (seed : Seed)
    (leaf : Leaf (t+1)) (j : Fin (m+1))
    (he : 0<ControllerEarlyEvents.count (rules (ell := ell) K (decode t θ))
      (ControllerPolicyTrace.withOutput P (ordinaryJet (scalar K t (decode t θ)))
        (richJet (scalar K t (decode t θ))) N seed) TaskState.initial (leaf,j)) :
    ∃ i<(N+1)*(8^(t+1)+4), ∃ n b output p s,
      run P (suppress (rules (ell := ell) K (decode t θ)) (blockLeaf leaf)) (taskDisclosed leaf j)
        (ordinaryReply K t θ) (richReply K t θ) i
        (ControllerPolicyDriver.initial P N seed TaskState.initial)=
        .pending n b output (.normal p s) ∧ IsEarlyFor (rules K (decode t θ)) p s (leaf,j) ∧
          taskDisclosed leaf j s=false := by
  obtain ⟨i,hi,n,b,output,p,s,hr,hearly⟩ :=
    GeometricEarlyRealization.original_early_has_normal_phase t P hK θ hd hell N seed leaf j he
  have hopen : taskDisclosed leaf j s=false := by
    apply decide_eq_false
    have hj := hearly.2.1
    change (s.completed leaf).val=j.val at hj
    omega
  have hretire : ∀ u : State (t+1) (m+1) ell,Ready u → ∀ a : Action t m,
      taskDisclosed leaf j u=true → taskDisclosed leaf j (retireNode u (target a))=true := by
    intro u _ a hu
    exact taskDisclosed_completed_mono leaf j u _ (retireSet_completed_mono u _) hu
  have hnormal : ∀ u : State (t+1) (m+1) ell,Ready u → ∀ p,
      taskDisclosed leaf j u=true → taskDisclosed leaf j (normal (rules K (decode t θ)) p u)=true := by
    intro u hu p hstop
    exact taskDisclosed_completed_mono leaf j u _ (normal_completed_mono _ p hu) hstop
  have hc := ControllerOpenSuppression.guarded_run_eq_of_open_endpoint P (rules K (decode t θ))
    (blockLeaf leaf) (taskDisclosed leaf j) (completedOrdinary K t θ) (completedRich K t θ)
    hell hretire hnormal (blocked_retires_target leaf j)
    (ControllerPolicyDriver.initial P N seed TaskState.initial) (initial_ready hell) i
    (by rw [hr]; exact hopen)
  rw [hr] at hc
  rw [CensoredOriginalExecution.completed_guarded_run t P K θ _ (taskDisclosed leaf j)
    (GeometricStoppedEarly.task_stop_active leaf j)] at hc
  exact ⟨i,hi,n,b,output,p,s,hc,hearly,hopen⟩

end GradientHessian.GeometricSuppressedEarly
