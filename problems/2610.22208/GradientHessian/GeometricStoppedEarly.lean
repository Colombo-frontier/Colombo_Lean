import GradientHessian.GeometricEarlyRealization
import GradientHessian.ControllerDriverMonotonicity
import GradientHessian.GeometricDisclosureStops

/-! A genuine early target completion occurs before its disclosure stop.
The stopped run therefore reaches the same normal phase and pending point. -/

noncomputable section
namespace GradientHessian.GeometricStoppedEarly
universe u
open Classical HigherHierarchy HierarchyParameters CensoredOracle ControllerCensor
  FrontierState TaskState TaskSlots ComparisonController GeometricRepair JetLocality
  CensoredPolicy ControllerPolicyDriver ControllerNormalRealization GeometricDisclosure
  ComparisonControllerReplay ControllerDriverMonotonicity VisibilityWindow VisibilityTaskWindow

theorem task_stop_active {L M ell : ℕ} (leaf : Leaf L) (j : Fin M)
    (s : State L M ell) (hs : taskDisclosed leaf j s=false) : TaskState.current s≠none := by
  intro hc
  have he := (FrontierState.current_none_iff (TaskState.retired s)).mp hc
  have hl : leaf∈TaskState.retired s := he ▸ Finset.mem_univ leaf
  have hm := (mem_retired s leaf).mp hl
  have hn := of_decide_eq_false hs
  exact hn (by omega)

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

theorem original_early_has_stopped_normal_phase {K : ℝ} (hK : 0<K) (θ : Parameters Y E H m t)
    (hd : Valid Y E H m t (decode t θ)) (hell : 0<ell) (N : ℕ) (seed : Seed)
    (leaf : Leaf (t+1)) (j : Fin (m+1))
    (he : 0<ControllerEarlyEvents.count (rules (ell := ell) K (decode t θ))
      (ControllerPolicyTrace.withOutput P (ordinaryJet (scalar K t (decode t θ)))
        (richJet (scalar K t (decode t θ))) N seed) TaskState.initial (leaf,j)) :
    ∃ i<(N+1)*(8^(t+1)+4), ∃ n b output p s,
      run P (rules (ell := ell) K (decode t θ)) (taskDisclosed leaf j)
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
  have hc := guarded_eq_at_open_endpoint P (rules K (decode t θ)) (taskDisclosed leaf j)
    (completedOrdinary K t θ) (completedRich K t θ) hell hretire hnormal
    (ControllerPolicyDriver.initial P N seed TaskState.initial) (initial_ready hell) i
    (by rw [hr]; exact hopen)
  rw [hr] at hc
  rw [CensoredOriginalExecution.completed_guarded_run t P K θ _ (taskDisclosed leaf j)
    (task_stop_active leaf j)] at hc
  exact ⟨i,hi,n,b,output,p,s,hc,hearly,hopen⟩

end GradientHessian.GeometricStoppedEarly
