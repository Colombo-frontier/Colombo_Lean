import GradientHessian.AugmentedPolicyReplies
import GradientHessian.ControllerAdaptiveExecution

/-! Saved-state replay for the full disclosure oracle. Initialization reads
the public packet before selecting any point. Until the target stop, both
that initialization and every subsequent augmented reply ignore the target. -/

noncomputable section
namespace GradientHessian.AugmentedPolicy
open Classical HigherHierarchy HierarchyAddresses RawHierarchy RawDirection
  FrontierState TaskState GeometricRepair GeometricDisclosure AugmentedDisclosure
  ComparisonController ComparisonControllerReplay

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]
variable [∀ t,MeasurableSpace (DirectionPolicyReplay.Point d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Rich d J E H t)]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)

def initial (t : ℕ)
    (policy : Machine.Policy (Seed × Packet d J E H t ell) S (DirectionPolicyReplay.Point d J E H t)
      (Ordinary d J E H t ell) (Rich d J E H t ell))
    (K : ℝ) (x : Raw d n r J E H t) (N : ℕ) (seed : Seed) (s : State (t+1) (4096*J^2+1) ell) :
    ControllerPolicyDriver.Config (t+1) (4096*J^2+1) ell S (DirectionPolicyReplay.Point d J E H t) (Action t (4096*J^2)) :=
  ControllerPolicyDriver.initial policy N (seed,view K (assemble P B fallback t x) s) s

def run (t : ℕ)
    (policy : Machine.Policy (Seed × Packet d J E H t ell) S (DirectionPolicyReplay.Point d J E H t)
      (Ordinary d J E H t ell) (Rich d J E H t ell))
    (K : ℝ) (blocked : Action t (4096*J^2) → Bool) (stop : State (t+1) (4096*J^2+1) ell → Bool)
    (x : Raw d n r J E H t) (fuel : ℕ)
    (q : ControllerPolicyDriver.Config (t+1) (4096*J^2+1) ell S (DirectionPolicyReplay.Point d J E H t) (Action t (4096*J^2))) :=
  ControllerPolicyDriver.run policy (suppress (rules K (assemble P B fallback t x)) blocked) stop
    (ordinary P B fallback K t x) (rich P B fallback K t x) fuel q

def trajectory (t : ℕ)
    (policy : Machine.Policy (Seed × Packet d J E H t ell) S (DirectionPolicyReplay.Point d J E H t)
      (Ordinary d J E H t ell) (Rich d J E H t ell))
    (K : ℝ) (blocked : Action t (4096*J^2) → Bool) (stop : State (t+1) (4096*J^2+1) ell → Bool)
    (N : ℕ) (s : State (t+1) (4096*J^2+1) ell) (fuel : ℕ) (x : Raw d n r J E H t × Seed) :=
  run P B fallback t policy K blocked stop x.1 fuel (initial P B fallback t policy K x.1 N x.2 s)

theorem run_eq (t : ℕ)
    (policy : Machine.Policy (Seed × Packet d J E H t ell) S (DirectionPolicyReplay.Point d J E H t)
      (Ordinary d J E H t ell) (Rich d J E H t ell))
    (K : ℝ) (blocked : Action t (4096*J^2) → Bool) (stop : State (t+1) (4096*J^2+1) ell → Bool)
    (x y : Raw d n r J E H t)
    (ht : ∀ s,stop s=false → ∀ Z a,blocked a=false →
      trigger K (assemble P B fallback t x) s Z a=trigger K (assemble P B fallback t y) s Z a)
    (hh : ∀ s,stop s=false → ∀ Z,hit (assemble P B fallback t x) s Z=hit (assemble P B fallback t y) s Z)
    (hr : ∀ before after,stop before=false → stop after=false → ∀ Z,
      ordinary P B fallback K t x before after Z=ordinary P B fallback K t y before after Z ∧
      rich P B fallback K t x before after Z=rich P B fallback K t y before after Z)
    (fuel : ℕ) (q : ControllerPolicyDriver.Config (t+1) (4096*J^2+1) ell S
      (DirectionPolicyReplay.Point d J E H t) (Action t (4096*J^2))) :
    run P B fallback t policy K blocked stop x fuel q=run P B fallback t policy K blocked stop y fuel q := by
  unfold run
  apply ControllerPolicyDriver.run_congr policy
    (suppress (rules K (assemble P B fallback t x)) blocked)
    (suppress (rules K (assemble P B fallback t y)) blocked) stop rfl rfl
  · intro s hs Z a
    cases hb : blocked a with
    | true => simp only [suppress,hb,if_true]
    | false => simpa only [suppress,hb,Bool.false_eq_true,if_false] using ht s hs Z a hb
  · exact hh
  · intro before after hb ha Z; exact (hr before after hb ha Z).1
  · intro before after hb ha Z; exact (hr before after hb ha Z).2

theorem trajectory_eq (t : ℕ)
    (policy : Machine.Policy (Seed × Packet d J E H t ell) S (DirectionPolicyReplay.Point d J E H t)
      (Ordinary d J E H t ell) (Rich d J E H t ell))
    (K : ℝ) (blocked : Action t (4096*J^2) → Bool) (stop : State (t+1) (4096*J^2+1) ell → Bool)
    (x y : Raw d n r J E H t)
    (ht : ∀ s,stop s=false → ∀ Z a,blocked a=false →
      trigger K (assemble P B fallback t x) s Z a=trigger K (assemble P B fallback t y) s Z a)
    (hh : ∀ s,stop s=false → ∀ Z,hit (assemble P B fallback t x) s Z=hit (assemble P B fallback t y) s Z)
    (hr : ∀ before after,stop before=false → stop after=false → ∀ Z,
      ordinary P B fallback K t x before after Z=ordinary P B fallback K t y before after Z ∧
      rich P B fallback K t x before after Z=rich P B fallback K t y before after Z)
    (N : ℕ) (s : State (t+1) (4096*J^2+1) ell)
    (hv : view K (assemble P B fallback t x) s=view K (assemble P B fallback t y) s)
    (fuel : ℕ) (seed : Seed) :
    trajectory P B fallback t policy K blocked stop N s fuel (x,seed)=
      trajectory P B fallback t policy K blocked stop N s fuel (y,seed) := by
  unfold trajectory
  have hi : initial P B fallback t policy K x N seed s=initial P B fallback t policy K y N seed s := by
    simp only [initial,hv]
  rw [hi]
  exact run_eq P B fallback t policy K blocked stop x y ht hh hr fuel _

theorem center_trajectory_eq {K : ℝ} (hK : 0<K) (h depth : ℕ) (w : Word depth) (i : Fin 8)
    (x y : Raw d n r J E H (h+1+depth))
    (he : (RawCenterFactor.factor h depth w i x).2=(RawCenterFactor.factor h depth w i y).2)
    (policy : Machine.Policy (Seed × Packet d J E H (h+1+depth) ell) S
      (DirectionPolicyReplay.Point d J E H (h+1+depth)) (Ordinary d J E H (h+1+depth) ell) (Rich d J E H (h+1+depth) ell))
    (N : ℕ) (s : State (h+1+depth+1) (4096*J^2+1) ell)
    (hs : DirectionPolicyReplay.centerStop h depth w i s=false) (fuel : ℕ) (seed : Seed) :
    trajectory P B fallback (h+1+depth) policy K (blockDirection (embed (h+1) depth w (.inr i)))
      (DirectionPolicyReplay.centerStop h depth w i) N s fuel (x,seed)=
    trajectory P B fallback (h+1+depth) policy K (blockDirection (embed (h+1) depth w (.inr i)))
      (DirectionPolicyReplay.centerStop h depth w i) N s fuel (y,seed) := by
  have ht := center_rule_erasure (ell := ell) P B fallback K h depth w i x y he
  exact trajectory_eq P B fallback _ policy K _ _ x y (fun s _ => ht.1 s) (fun s _ => ht.2 s)
    (fun before after _ ha => center_replies_eq P B fallback hK h depth w i x y he before after ha)
    N s (center_view_eq P B fallback K h depth w i x y he s hs) fuel seed

theorem old_trajectory_eq {K : ℝ} (hK : 0<K) (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.oldFactor depth w i j x).2=(RawMemoryHierarchyFactor.oldFactor depth w i j y).2)
    (policy : Machine.Policy (Seed × Packet d J E H (0+depth) ell) S
      (DirectionPolicyReplay.Point d J E H (0+depth)) (Ordinary d J E H (0+depth) ell) (Rich d J E H (0+depth) ell))
    (N : ℕ) (s : State (0+depth+1) (4096*J^2+1) ell)
    (hs : DirectionPolicyReplay.oldStop depth w i s=false) (fuel : ℕ) (seed : Seed) :
    trajectory P B fallback (0+depth) policy K (blockDirection (embed 0 depth w (.inl (i,j))))
      (DirectionPolicyReplay.oldStop depth w i) N s fuel (x,seed)=
    trajectory P B fallback (0+depth) policy K (blockDirection (embed 0 depth w (.inl (i,j))))
      (DirectionPolicyReplay.oldStop depth w i) N s fuel (y,seed) := by
  have ht := old_rule_erasure (ell := ell) P B fallback K depth w i j x y he
  exact trajectory_eq P B fallback _ policy K _ _ x y (fun s _ => ht.1 s) (fun s _ => ht.2 s)
    (fun before after _ ha => old_replies_eq P B fallback hK depth w i j x y he before after ha)
    N s (old_view_eq P B fallback K depth w i j x y he s hs) fuel seed

theorem inner_trajectory_eq {K : ℝ} (hK : 0<K) (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.innerFactor depth w i j k x).2=(RawMemoryHierarchyFactor.innerFactor depth w i j k y).2)
    (policy : Machine.Policy (Seed × Packet d J E H (0+depth) ell) S
      (DirectionPolicyReplay.Point d J E H (0+depth)) (Ordinary d J E H (0+depth) ell) (Rich d J E H (0+depth) ell))
    (N : ℕ) (s : State (0+depth+1) (4096*J^2+1) ell)
    (hs : taskDisclosed (leafEquiv (0+depth) (prependSlot 0 depth w i)) j s=false) (fuel : ℕ) (seed : Seed) :
    trajectory P B fallback (0+depth) policy K (blockDirection (embed 0 depth w (.inr (i,j,k))))
      (taskDisclosed (leafEquiv (0+depth) (prependSlot 0 depth w i)) j) N s fuel (x,seed)=
    trajectory P B fallback (0+depth) policy K (blockDirection (embed 0 depth w (.inr (i,j,k))))
      (taskDisclosed (leafEquiv (0+depth) (prependSlot 0 depth w i)) j) N s fuel (y,seed) := by
  have ht := inner_rule_erasure (ell := ell) P B fallback K depth w i j k x y he
  exact trajectory_eq P B fallback _ policy K _ _ x y (fun s _ => ht.1 s) (fun s _ => ht.2 s)
    (fun before after _ ha => inner_replies_eq P B fallback hK depth w i j k x y he before after ha)
    N s (inner_view_eq P B fallback K depth w i j k x y he s hs) fuel seed

theorem mark_trajectory_eq {K : ℝ} (hK : 0<K) (t : ℕ) (leaf : Leaf (t+1)) (j : Fin (4096*J^2+1))
    (x y : Raw d n r J E H t)
    (he : (RawMarkFactor.factor t ((leafEquiv t).symm leaf) j x).2=(RawMarkFactor.factor t ((leafEquiv t).symm leaf) j y).2)
    (policy : Machine.Policy (Seed × Packet d J E H t ell) S
      (DirectionPolicyReplay.Point d J E H t) (Ordinary d J E H t ell) (Rich d J E H t ell))
    (N : ℕ) (s : State (t+1) (4096*J^2+1) ell) (hs : markStop leaf j s=false) (fuel : ℕ) (seed : Seed) :
    trajectory P B fallback t policy K (blockMark leaf j) (markStop leaf j) N s fuel (x,seed)=
      trajectory P B fallback t policy K (blockMark leaf j) (markStop leaf j) N s fuel (y,seed) := by
  apply trajectory_eq P B fallback t policy K _ _ x y
  · intro s _ Z a ha
    exact mark_other_trigger_eq P B fallback t leaf j x y he K s Z a (of_decide_eq_false ha)
  · intro s hs Z
    exact mark_normal_hit_eq P B fallback t leaf j x y he s (markStop_open leaf j s hs) Z
  · exact mark_replies_eq P B fallback hK t leaf j x y he
  · exact mark_view_eq P B fallback K t leaf j x y he s hs

end GradientHessian.AugmentedPolicy
