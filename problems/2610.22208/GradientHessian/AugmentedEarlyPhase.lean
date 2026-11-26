import GradientHessian.AugmentedPolicyEvents
import GradientHessian.ControllerAdaptiveEarly
import GradientHessian.GeometricMaskedEarly

noncomputable section
namespace GradientHessian.AugmentedEarlyPhase
open Classical HigherHierarchy HierarchyAddresses RawHierarchy FrontierState TaskState TaskSlots
  GeometricRepair GeometricDisclosure AugmentedDisclosure ComparisonController ComparisonControllerReplay
  AugmentedPolicy ControllerPolicyDriver ControllerNormalRealization ControllerDriverMonotonicity
  VisibilityWindow VisibilityTaskWindow NumericalShadowRules

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]
variable [∀ t,MeasurableSpace (DirectionPolicyReplay.Point d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Rich d J E H t)]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (policy : Machine.Policy (Seed × Packet d J E H t ell) S (DirectionPolicyReplay.Point d J E H t)
    (Ordinary d J E H t ell) (Rich d J E H t ell))

def earlyEvent (K : ℝ) (N : ℕ) (leaf : Leaf (t+1)) (j : Fin (4096*J^2+1)) :
    Set (Raw d n r J E H t × Seed) :=
  {x | 0<ControllerEarlyEvents.count (rules (ell := ell) K (assemble P B fallback t x.1))
    (selectedPoints P B fallback t policy K N TaskState.initial x) TaskState.initial (leaf,j)}

def earlyCount (K : ℝ) (N : ℕ) (x : Raw d n r J E H t × Seed) : ℕ :=
  ComparisonControllerLedger.tally (rules (ell := ell) K (assemble P B fallback t x.1))
    (ComparisonControllerLedger.early (rules (ell := ell) K (assemble P B fallback t x.1)))
    (selectedPoints P B fallback t policy K N TaskState.initial x) TaskState.initial

theorem masked_normal_phase (K : ℝ) (hell : 0<ell) (N : ℕ)
    (x : Raw d n r J E H t × Seed) (leaf : Leaf (t+1)) (j : Fin (4096*J^2+1))
    (he : x∈earlyEvent P B fallback t policy K N leaf j) :
    ∃ i<(N+1)*(8^(t+1)+4),∃ rem a output p u,
      ControllerPolicyDriver.run policy
        (ControllerHitMasking.mask (suppress (rules K (assemble P B fallback t x.1)) (blockLeaf leaf))
          (GeometricMaskedEarly.targetTask leaf j)) (fun _ => false)
        (AugmentedPolicy.ordinary P B fallback K t x.1) (AugmentedPolicy.rich P B fallback K t x.1)
        i (AugmentedPolicy.initial P B fallback t policy K x.1 N x.2 TaskState.initial)=
          .pending rem a output (.normal p u) ∧
      IsEarlyFor (rules K (assemble P B fallback t x.1)) p u (leaf,j) ∧ taskDisclosed leaf j u=false := by
  obtain ⟨i,hi,rem,a,output,p,u,hu,hearly⟩ := ControllerAdaptiveEarly.early_realized policy
    (rules K (assemble P B fallback t x.1))
    (AugmentedPolicy.ordinary P B fallback K t x.1) (AugmentedPolicy.rich P B fallback K t x.1)
    N (policy.initial (x.2,view K (assemble P B fallback t x.1) TaskState.initial))
    TaskState.initial (leaf,j) he
  have hopen : taskDisclosed leaf j u=false := by
    apply decide_eq_false
    have hj := hearly.2.1
    change (u.completed leaf).val=j.val at hj
    change ¬j.val<(u.completed leaf).val
    omega
  have hretire : ∀ s : State (t+1) (4096*J^2+1) ell,Ready s → ∀ act : Action t (4096*J^2),
      taskDisclosed leaf j s=true → taskDisclosed leaf j (retireNode s (target act))=true := by
    intro s _ act hs
    exact taskDisclosed_completed_mono leaf j s _ (retireSet_completed_mono s _) hs
  have hnormal (R : Rules (t+1) (4096*J^2+1) ell (DirectionPolicyReplay.Point d J E H t) (Action t (4096*J^2))) :
      ∀ s,Ready s → ∀ p,taskDisclosed leaf j s=true → taskDisclosed leaf j (normal R p s)=true := by
    intro s hs p hh
    exact taskDisclosed_completed_mono leaf j s _ (normal_completed_mono R p hs) hh
  have hsupp := ControllerOpenSuppression.run_eq_of_open_endpoint policy
    (rules K (assemble P B fallback t x.1)) (blockLeaf leaf) (taskDisclosed leaf j)
    (AugmentedPolicy.ordinary P B fallback K t x.1) (AugmentedPolicy.rich P B fallback K t x.1)
    hell hretire (hnormal _) (GeometricSuppressedEarly.blocked_retires_target leaf j)
    (AugmentedPolicy.initial P B fallback t policy K x.1 N x.2 TaskState.initial)
    (initial_ready hell) i (by dsimp only [AugmentedPolicy.initial,ControllerPolicyDriver.initial]; rw [hu]; exact hopen)
  have hsupp' := hsupp.symm.trans hu
  have hmask := ControllerHitMasking.run_eq_of_open_endpoint policy
    (suppress (rules K (assemble P B fallback t x.1)) (blockLeaf leaf))
    (GeometricMaskedEarly.targetTask leaf j) (taskDisclosed leaf j)
    (AugmentedPolicy.ordinary P B fallback K t x.1) (AugmentedPolicy.rich P B fallback K t x.1)
    hell hretire (hnormal _) (GeometricMaskedEarly.target_hit_closes _ leaf j)
    (AugmentedPolicy.initial P B fallback t policy K x.1 N x.2 TaskState.initial)
    (initial_ready hell) i (by rw [hsupp']; exact hopen)
  exact ⟨i,hi,rem,a,output,p,u,hmask.symm.trans hsupp',hearly,hopen⟩

end GradientHessian.AugmentedEarlyPhase
