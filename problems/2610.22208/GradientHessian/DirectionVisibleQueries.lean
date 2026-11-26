import GradientHessian.DirectionPolicyMeasurability
import GradientHessian.ControllerVisibleSelections
import GradientHessian.ControllerPolicyTraceInvariant

/-! Actual direction shadows produce measurable visible-point arrays with
the exact subtree cap. The array is a function only of the original external
factor and private seed; its cap and repair-phase coverage are proved. -/

noncomputable section
namespace GradientHessian.DirectionVisibleQueries
open Classical HigherHierarchy HierarchyAddresses RawHierarchy HierarchyParameters
  FrontierState TaskState TaskSlots GeometricRepair ComparisonController ComparisonControllerReplay
  ControllerMeasurable RawDirection DirectionPolicyReplay

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable [∀ t,MeasurableSpace (Point d J E H t)] [∀ t,BorelSpace (Point d J E H t)]
  [∀ t,MeasurableSpace (Ordinary d J E H t)] [∀ t,BorelSpace (Ordinary d J E H t)]
  [∀ t,MeasurableSpace (Rich d J E H t)] [∀ t,BorelSpace (Rich d J E H t)]
variable {Seed S V W : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
  [MeasurableSpace V] [MeasurableSpace W]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (target : Slot J t) (stop : State (t+1) (4096*J^2+1) ell → Bool)
  (e : Raw d n r J E H t ≃ᵐ V × W) (replacement : V)
  (policy : Machine.Policy Seed S (Point d J E H t) (Ordinary d J E H t) (Rich d J E H t))

def restore (rest : W) : Raw d n r J E H t := e.symm (replacement,rest)

def restRules (K : ℝ) (rest : W) : Rules (t+1) (4096*J^2+1) ell (Point d J E H t) (Action t (4096*J^2)) :=
  suppress (rules K (assemble P B fallback t (restore t e replacement rest))) (blockDirection target)

def trajectory (K : ℝ) (N : ℕ) (s₀ : State (t+1) (4096*J^2+1) ell) (i : ℕ) (w : W × Seed) :
    ControllerPolicyDriver.Config (t+1) (4096*J^2+1) ell S (Point d J E H t) (Action t (4096*J^2)) :=
  DirectionPolicyReplay.shadow P B fallback t target stop policy e replacement K w.1 i
    (ControllerPolicyDriver.initial policy N w.2 s₀)

def entries (K : ℝ) (N fuel : ℕ) (s₀ : State (t+1) (4096*J^2+1) ell) :
    ControllerOptionalTrajectory.Schedule (W × Seed) (Point d J E H t) :=
  ControllerPolicyDriver.schedule policy stop
    (trajectory P B fallback t target stop e replacement policy K N s₀) fuel

def physicalQuery (v : Node (t+1)) (K : ℝ) (N fuel : ℕ) (s₀ : State (t+1) (4096*J^2+1) ell)
    (i : ℕ) (w : W × Seed) : Point d J E H t :=
  ControllerVisibleSelections.queryAt (priority t (4096*J^2)) GeometricRepair.target
    (fun w => (restRules (ell := ell) P B fallback t target e replacement K w.1).trigger)
    (fun w => (restRules (ell := ell) P B fallback t target e replacement K w.1).hit)
    v (entries P B fallback t target stop e replacement policy K N fuel s₀) (fun _ => s₀) 0 i w

def cap (v : Node (t+1)) : ℕ := 8^(t+1-v.1.val)*(4096*J^2+1)*ell

def query (v : Node (t+1)) (K : ℝ) (N fuel : ℕ) (s₀ : State (t+1) (4096*J^2+1) ell)
    (w : W × Seed) (i : Fin (cap (J := J) (ell := ell) t v)) : Point d J E H t :=
  physicalQuery P B fallback t target stop e replacement policy v K N fuel s₀ i.val w

theorem trajectory_measurable {K : ℝ} (hK : 0<K) (N : ℕ) (s₀ : State (t+1) (4096*J^2+1) ell) (i : ℕ) :
    Measurable (trajectory P B fallback t target stop e replacement policy K N s₀ i) :=
  DirectionPolicyReplay.shadow_seed_measurable P B fallback t target stop policy e replacement hK i N s₀

theorem entries_measurable {K : ℝ} (hK : 0<K) (N fuel : ℕ) (s₀ : State (t+1) (4096*J^2+1) ell) :
    ControllerOptionalTrajectory.IsMeasurable (entries P B fallback t target stop e replacement policy K N fuel s₀) :=
  ControllerPolicyDriver.schedule_measurable policy stop _
    (trajectory_measurable P B fallback t target stop e replacement policy hK N s₀) fuel

theorem restore_measurable : Measurable (restore t e replacement) :=
  e.symm.measurable.comp (measurable_const.prodMk measurable_id)

theorem rest_trigger_measurable (K : ℝ) (s : State (t+1) (4096*J^2+1) ell) (a : Action t (4096*J^2)) :
    Measurable (fun q : (W × Seed) × Point d J E H t =>
      (restRules (ell := ell) P B fallback t target e replacement K q.1.1).trigger s q.2 a) := by
  cases hb : blockDirection target a with
  | true => simp only [restRules,suppress,hb,if_true]; exact measurable_const
  | false =>
    have hmap : Measurable (fun q : (W × Seed) × Point d J E H t => (restore t e replacement q.1.1,q.2)) :=
      (((restore_measurable t e replacement).comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
    have hc := (trigger_fixed_joint_measurable (n := n) (E := E) (H := H) P B fallback t K s a).comp hmap
    simpa only [restRules,suppress,hb,Bool.false_eq_true,if_false,Function.comp_def] using hc

theorem rest_hit_measurable (s : State (t+1) (4096*J^2+1) ell) :
    Measurable (fun q : (W × Seed) × Point d J E H t =>
      (restRules (ell := ell) P B fallback t target e replacement 1 q.1.1).hit s q.2) := by
  have hmap : Measurable (fun q : (W × Seed) × Point d J E H t => (restore t e replacement q.1.1,q.2)) :=
    (((restore_measurable t e replacement).comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
  have hc := (hit_fixed_joint_measurable (n := n) (E := E) (H := H) P B fallback t s).comp hmap
  simpa only [restRules,suppress,Function.comp_def] using hc

theorem physicalQuery_measurable (v : Node (t+1)) {K : ℝ} (hK : 0<K) (N fuel : ℕ)
    (s₀ : State (t+1) (4096*J^2+1) ell) (i : ℕ) :
    Measurable (physicalQuery P B fallback t target stop e replacement policy v K N fuel s₀ i) := by
  unfold physicalQuery
  apply ControllerVisibleSelections.queryAt_measurable (Ω := W × Seed) (X := Point d J E H t)
    (priority t (4096*J^2)) GeometricRepair.target
    (fun w => (restRules (ell := ell) P B fallback t target e replacement K w.1).trigger)
    (fun w => (restRules (ell := ell) P B fallback t target e replacement K w.1).hit)
  · exact rest_trigger_measurable P B fallback t target e replacement K
  · exact rest_hit_measurable P B fallback t target e replacement
  · exact entries_measurable P B fallback t target stop e replacement policy hK N fuel s₀
  · exact measurable_const

theorem query_measurable (v : Node (t+1)) {K : ℝ} (hK : 0<K) (N fuel : ℕ)
    (s₀ : State (t+1) (4096*J^2+1) ell) (i : Fin (cap (J := J) (ell := ell) t v)) :
    Measurable (fun w => query P B fallback t target stop e replacement policy v K N fuel s₀ w i) :=
  physicalQuery_measurable P B fallback t target stop e replacement policy v hK N fuel s₀ i.val

theorem entries_selected (K : ℝ) (N fuel : ℕ) (s₀ : State (t+1) (4096*J^2+1) ell) (w : W × Seed) :
    ControllerOptionalTrajectory.selected (entries P B fallback t target stop e replacement policy K N fuel s₀) w=
      ControllerPolicyDriver.selections policy (restRules (ell := ell) P B fallback t target e replacement K w.1) stop
        (DirectionPolicy.ordinary K t (coefficients P B fallback t (restore t e replacement w.1)))
        (DirectionPolicy.rich K t (coefficients P B fallback t (restore t e replacement w.1))) fuel
        (ControllerPolicyDriver.initial policy N w.2 s₀) := by
  simpa only [entries,trajectory,DirectionPolicyReplay.shadow,DirectionPolicyReplay.run,restore,restRules,
    ControllerPolicyDriver.selections] using ControllerPolicyDriver.schedule_selected policy stop
      (trajectory P B fallback t target stop e replacement policy K N s₀) fuel w

theorem visible_covered (v : Node (t+1)) (K : ℝ) (N fuel : ℕ) (s₀ : State (t+1) (4096*J^2+1) ell)
    (hs : Ready s₀) (hell : 0<ell) (w : W × Seed) {Z : Point d J E H t}
    (hZ : Z ∈ seenPoints (restRules (ell := ell) P B fallback t target e replacement K w.1) v
      (ControllerOptionalTrajectory.selected (entries P B fallback t target stop e replacement policy K N fuel s₀) w) s₀) :
    ∃ i : Fin (cap (J := J) (ell := ell) t v),query P B fallback t target stop e replacement policy v K N fuel s₀ w i=Z := by
  exact ControllerVisibleSelections.visible_array_covers (Ω := W × Seed)
    (priority t (4096*J^2)) GeometricRepair.target
    (fun w => (restRules (ell := ell) P B fallback t target e replacement K w.1).trigger)
    (fun w => (restRules (ell := ell) P B fallback t target e replacement K w.1).hit)
    v (entries P B fallback t target stop e replacement policy K N fuel s₀) (fun _ => s₀) 0 w hs hell hZ

theorem repairing_covered (v : Node (t+1)) (K : ℝ) (N fuel : ℕ) (s₀ : State (t+1) (4096*J^2+1) ell)
    (hs : Ready s₀) (hell : 0<ell) (w : W × Seed) (i : ℕ) (hi : i≤fuel)
    (remaining : ℕ) (a : S) (output : Bool) (p : Pending (Point d J E H t)) (s : State (t+1) (4096*J^2+1) ell)
    (hp : trajectory P B fallback t target stop e replacement policy K N s₀ i w=.pending remaining a output (.repairing p s))
    (hv : Visible (TaskState.retired s) v) :
    ∃ q : Fin (cap (J := J) (ell := ell) t v),query P B fallback t target stop e replacement policy v K N fuel s₀ w q=p.point := by
  have hm := ControllerPolicyTraceInvariant.repairing_visible_mem policy
    (restRules (ell := ell) P B fallback t target e replacement K w.1) stop
    (DirectionPolicy.ordinary K t (coefficients P B fallback t (restore t e replacement w.1)))
    (DirectionPolicy.rich K t (coefficients P B fallback t (restore t e replacement w.1)))
    N w.2 s₀ i fuel hi remaining a output p s v hp hv
  rw [← entries_selected P B fallback t target stop e replacement policy K N fuel s₀ w] at hm
  exact visible_covered P B fallback t target stop e replacement policy v K N fuel s₀ hs hell w hm

end GradientHessian.DirectionVisibleQueries
