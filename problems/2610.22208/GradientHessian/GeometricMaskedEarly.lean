import GradientHessian.GeometricSuppressedEarly
import GradientHessian.ControllerHitMasking

/-! The target task's true hit feedback can be removed before its actual
early normal phase. The query point is retained before feedback is applied. -/

noncomputable section
namespace GradientHessian.GeometricMaskedEarly
universe u
open Classical HigherHierarchy HierarchyParameters CensoredOracle ControllerCensor
  FrontierState TaskState TaskSlots ComparisonController GeometricRepair JetLocality
  CensoredPolicy ControllerPolicyDriver ControllerNormalRealization GeometricDisclosure
  ComparisonControllerReplay ControllerDriverMonotonicity VisibilityWindow VisibilityTaskWindow
  NumericalShadowRules

def targetTask {L M ell : ℕ} (leaf : Leaf L) (j : Fin M) (s : State L M ell) : Bool :=
  decide (TaskState.current s=some leaf ∧ (s.completed leaf).val=j.val)

theorem target_hit_closes {L M ell : ℕ} {X A : Type*} (R : Rules L M ell X A)
    (leaf : Leaf L) (j : Fin M) (s : State L M ell) (hs : Ready s) (p : Pending X)
    (hk : p.kind=.ordinary) (ht : targetTask leaf j s=true) (hh : R.hit s p.point=true) :
    taskDisclosed leaf j (normal R p s)=true := by
  obtain ⟨hc,hj⟩ := of_decide_eq_true ht
  have hl := current_live s hc
  have hla : ((advanceSlot s leaf).completed leaf).val < M := by simpa using hl
  apply decide_eq_true
  change j.val < ((normal R p s).completed leaf).val
  rw [normal,hk,ordinaryStep_eq _ s hc (hs.2 leaf hl),if_pos (Or.inl hh),
    completeLeaf_completed _ _ hla,advanceSlot_completed,hj]
  omega

theorem target_task_guarded_run {L M ell : ℕ} {Seed S X Y Z A : Type*}
    [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z]
    (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (leaf : Leaf L) (j : Fin M)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z) (hell : 0<ell)
    (q : Config L M ell S X A) (hq : Coherent (taskDisclosed leaf j) q) (N : ℕ)
    (hN : taskDisclosed leaf j (stateOf (run P R (fun _ => false) ordinary rich N q))=false) :
    run P (ControllerHitMasking.mask R (targetTask leaf j)) (taskDisclosed leaf j) ordinary rich N q=
      run P R (fun _ => false) ordinary rich N q := by
  have hretire : ∀ s : State L M ell,Ready s → ∀ a,
      taskDisclosed leaf j s=true → taskDisclosed leaf j (retireNode s (R.target a))=true := by
    intro s _ a h
    exact taskDisclosed_completed_mono leaf j s _ (retireSet_completed_mono s _) h
  have hn (R' : Rules L M ell X A) : ∀ s : State L M ell,Ready s → ∀ p,
      taskDisclosed leaf j s=true → taskDisclosed leaf j (normal R' p s)=true := by
    intro s hs p h
    exact taskDisclosed_completed_mono leaf j s _ (normal_completed_mono R' p hs) h
  have he := ControllerHitMasking.run_eq_of_open_endpoint P R (targetTask leaf j)
    (taskDisclosed leaf j) ordinary rich hell hretire (hn R) (target_hit_closes R leaf j) q hq N hN
  rw [guarded_eq_at_open_endpoint P (ControllerHitMasking.mask R (targetTask leaf j))
    (taskDisclosed leaf j) ordinary rich hell hretire (hn _) q hq N (by rw [← he]; exact hN)]
  exact he.symm

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

theorem original_early_has_masked_normal_phase {K : ℝ} (hK : 0<K) (θ : Parameters Y E H m t)
    (hd : Valid Y E H m t (decode t θ)) (hell : 0<ell) (N : ℕ) (seed : Seed)
    (leaf : Leaf (t+1)) (j : Fin (m+1))
    (he : 0<ControllerEarlyEvents.count (rules (ell := ell) K (decode t θ))
      (ControllerPolicyTrace.withOutput P (ordinaryJet (scalar K t (decode t θ)))
        (richJet (scalar K t (decode t θ))) N seed) TaskState.initial (leaf,j)) :
    ∃ i<(N+1)*(8^(t+1)+4), ∃ n b output p s,
      run P (ControllerHitMasking.mask
        (suppress (rules (ell := ell) K (decode t θ)) (blockLeaf leaf)) (targetTask leaf j))
        (taskDisclosed leaf j) (ordinaryReply K t θ) (richReply K t θ) i
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
  have hc := ControllerOpenSuppression.run_eq_of_open_endpoint P (rules K (decode t θ))
    (blockLeaf leaf) (taskDisclosed leaf j) (completedOrdinary K t θ) (completedRich K t θ)
    hell hretire hnormal (GeometricSuppressedEarly.blocked_retires_target leaf j)
    (ControllerPolicyDriver.initial P N seed TaskState.initial) (initial_ready hell) i
    (by rw [hr]; exact hopen)
  have hr' := hc.symm.trans hr
  have hm := target_task_guarded_run P (suppress (rules K (decode t θ)) (blockLeaf leaf)) leaf j
    (completedOrdinary K t θ) (completedRich K t θ) hell
    (ControllerPolicyDriver.initial P N seed TaskState.initial) (initial_ready hell) i
    (by rw [hr']; exact hopen)
  rw [hr'] at hm
  rw [CensoredOriginalExecution.completed_guarded_run t P K θ _ (taskDisclosed leaf j)
    (GeometricStoppedEarly.task_stop_active leaf j)] at hm
  exact ⟨i,hi,n,b,output,p,s,hm,hearly,hopen⟩

end GradientHessian.GeometricMaskedEarly
