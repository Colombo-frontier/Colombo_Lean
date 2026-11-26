import GradientHessian.MarkPolicyMeasurability
import GradientHessian.ControllerVisibleSelections
import GradientHessian.ControllerPolicyTraceInvariant
import GradientHessian.RawFactorCoefficients

/-! The actual future-mark shadow supplies a measurable array of at most
M ell normalized tests for the marked leaf. It depends only on the
original raw factor's external coordinate and the private policy seed. -/

noncomputable section
namespace GradientHessian.MarkVisibleQueries
open Classical HigherHierarchy HierarchyAddresses RawHierarchy HierarchyParameters
open FrontierState TaskState TaskSlots GeometricRepair ComparisonController ComparisonControllerReplay
open ControllerMeasurable

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (leaf : Leaf (t+1)) (j : Fin (4096*J^2+1))

variable [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)] [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [MeasurableSpace (ℝ × ((Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) →L[ℝ] ℝ))] [BorelSpace (ℝ × ((Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) →L[ℝ] ℝ))] [MeasurableSpace (ℝ × ((Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) →L[ℝ] ℝ) × ((Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) →L[ℝ] (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) →L[ℝ] ℝ))] [BorelSpace (ℝ × ((Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) →L[ℝ] ℝ) × ((Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) →L[ℝ] (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) →L[ℝ] ℝ))]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (policy : Machine.Policy Seed S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (ℝ × ((Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) →L[ℝ] ℝ)) (ℝ × ((Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) →L[ℝ] ℝ) × ((Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) →L[ℝ] (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) →L[ℝ] ℝ)))

def restore (rest : (RawMarkFactor.Rest d n r J E H t)) : Raw d n r J E H t :=
  (RawMarkFactor.factor t ((leafEquiv t).symm leaf) j).symm (0,rest)

def restRules (K : ℝ) (rest : (RawMarkFactor.Rest d n r J E H t)) : Rules (t+1) (4096*J^2+1) ell (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Action t (4096*J^2)) :=
  suppress (rules K (assemble P B fallback t (restore t leaf j rest))) (blockMark leaf j)

def trajectory (K : ℝ) (N : ℕ) (s₀ : (State (t+1) (4096*J^2+1) ell)) (i : ℕ) (w : (RawMarkFactor.Rest d n r J E H t) × Seed) :
    ControllerPolicyDriver.Config (t+1) (4096*J^2+1) ell S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Action t (4096*J^2)) :=
  MarkPolicyReplay.shadow P B fallback t leaf j policy K w.1 i
    (ControllerPolicyDriver.initial policy N w.2 s₀)

def entries (K : ℝ) (N fuel : ℕ) (s₀ : (State (t+1) (4096*J^2+1) ell)) : ControllerOptionalTrajectory.Schedule ((RawMarkFactor.Rest d n r J E H t) × Seed) (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :=
  ControllerPolicyDriver.schedule policy (markSupplied leaf j) (trajectory (n := n) P B fallback t leaf j policy K N s₀) fuel

def physicalQuery (K : ℝ) (N fuel : ℕ) (s₀ : (State (t+1) (4096*J^2+1) ell)) (i : ℕ) (w : (RawMarkFactor.Rest d n r J E H t) × Seed) : (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :=
  ControllerVisibleSelections.queryAt (priority t (4096*J^2)) GeometricRepair.target
    (fun w => (restRules (ell := ell) P B fallback t leaf j K w.1).trigger)
    (fun w => (restRules (ell := ell) P B fallback t leaf j K w.1).hit)
    (leafNode leaf) (entries (n := n) P B fallback t leaf j policy K N fuel s₀) (fun _ => s₀) 0 i w

def query (K : ℝ) (N fuel : ℕ) (s₀ : (State (t+1) (4096*J^2+1) ell))
    (w : (RawMarkFactor.Rest d n r J E H t) × Seed) (i : Fin ((4096*J^2+1)*ell)) : EuclideanSpace ℝ (Fin d) :=
  BoundedNumericalTest.test (numericalProjection t (physicalQuery (n := n) P B fallback t leaf j policy K N fuel s₀ i.val w))

theorem trajectory_measurable {K : ℝ} (hK : 0<K) (N : ℕ) (s₀ : (State (t+1) (4096*J^2+1) ell)) (i : ℕ) :
    Measurable (trajectory (n := n) P B fallback t leaf j policy K N s₀ i) :=
  MarkPolicyReplay.shadow_seed_measurable (n := n) (E := E) (H := H) P B fallback t leaf j policy hK i N s₀

theorem entries_measurable {K : ℝ} (hK : 0<K) (N fuel : ℕ) (s₀ : (State (t+1) (4096*J^2+1) ell)) :
    ControllerOptionalTrajectory.IsMeasurable (entries (n := n) P B fallback t leaf j policy K N fuel s₀) :=
  ControllerPolicyDriver.schedule_measurable policy (markSupplied leaf j) _
    (trajectory_measurable (n := n) P B fallback t leaf j policy hK N s₀) fuel

theorem restore_measurable : Measurable (restore (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) t leaf j) :=
  (RawMarkFactor.factor t ((leafEquiv t).symm leaf) j).symm.measurable.comp (measurable_const.prodMk measurable_id)

theorem rest_trigger_measurable (K : ℝ) (s : (State (t+1) (4096*J^2+1) ell)) (a : (Action t (4096*J^2))) :
    Measurable (fun q : ((RawMarkFactor.Rest d n r J E H t) × Seed) × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) => (restRules (ell := ell) P B fallback t leaf j K q.1.1).trigger s q.2 a) := by
  cases hb : blockMark leaf j a with
  | true => simp only [restRules,suppress,hb,if_true]; exact measurable_const
  | false =>
    have hmap : Measurable (fun q : (RawMarkFactor.Rest d n r J E H t × Seed) ×
        Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t => (restore t leaf j q.1.1,q.2)) :=
      (((restore_measurable (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) t leaf j).comp
        (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
    have hc := (trigger_fixed_joint_measurable (n := n) (E := E) (H := H) P B fallback t K s a).comp hmap
    simpa only [restRules,suppress,hb,Bool.false_eq_true,if_false,Function.comp_def] using hc

theorem rest_hit_measurable (s : (State (t+1) (4096*J^2+1) ell)) :
    Measurable (fun q : ((RawMarkFactor.Rest d n r J E H t) × Seed) × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) => (restRules (ell := ell) P B fallback t leaf j 1 q.1.1).hit s q.2) := by
  have hmap : Measurable (fun q : (RawMarkFactor.Rest d n r J E H t × Seed) ×
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t => (restore t leaf j q.1.1,q.2)) :=
    (((restore_measurable (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) t leaf j).comp
      (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
  have hc := (hit_fixed_joint_measurable (n := n) (E := E) (H := H) P B fallback t s).comp hmap
  simpa only [restRules,suppress,Function.comp_def] using hc

theorem physicalQuery_measurable {K : ℝ} (hK : 0<K) (N fuel : ℕ) (s₀ : (State (t+1) (4096*J^2+1) ell)) (i : ℕ) :
    Measurable (physicalQuery (n := n) P B fallback t leaf j policy K N fuel s₀ i) := by
  unfold physicalQuery
  apply ControllerVisibleSelections.queryAt_measurable
    (Ω := RawMarkFactor.Rest d n r J E H t × Seed)
    (X := Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
    (priority t (4096*J^2)) GeometricRepair.target
    (fun w => (restRules (ell := ell) P B fallback t leaf j K w.1).trigger)
    (fun w => (restRules (ell := ell) P B fallback t leaf j K w.1).hit)
  · exact rest_trigger_measurable P B fallback t leaf j K
  · exact rest_hit_measurable P B fallback t leaf j
  · exact entries_measurable (n := n) P B fallback t leaf j policy hK N fuel s₀
  · exact measurable_const

theorem query_measurable {K : ℝ} (hK : 0<K) (N fuel : ℕ) (s₀ : (State (t+1) (4096*J^2+1) ell))
    (i : Fin ((4096*J^2+1)*ell)) :
    Measurable (fun w => query (n := n) P B fallback t leaf j policy K N fuel s₀ w i) :=
  BoundedNumericalTest.test_contDiff.continuous.measurable.comp
    ((numericalProjection (Y := EuclideanSpace ℝ (Fin d)) (E := E) (H := H) (m := 4096*J^2) t).continuous.measurable.comp
      (physicalQuery_measurable (n := n) P B fallback t leaf j policy hK N fuel s₀ i.val))

theorem query_norm (K : ℝ) (N fuel : ℕ) (s₀ : (State (t+1) (4096*J^2+1) ell)) (w : (RawMarkFactor.Rest d n r J E H t) × Seed)
    (i : Fin ((4096*J^2+1)*ell)) : ‖query (n := n) P B fallback t leaf j policy K N fuel s₀ w i‖≤1 :=
  BoundedNumericalTest.test_norm _

theorem entries_selected (K : ℝ) (N fuel : ℕ) (s₀ : (State (t+1) (4096*J^2+1) ell)) (w : (RawMarkFactor.Rest d n r J E H t) × Seed) :
    ControllerOptionalTrajectory.selected (entries (n := n) P B fallback t leaf j policy K N fuel s₀) w=
      ControllerPolicyDriver.selections policy (restRules (ell := ell) P B fallback t leaf j K w.1) (markSupplied leaf j)
        (MarkPolicyReplay.ordinary P B fallback t K (restore t leaf j w.1))
        (MarkPolicyReplay.rich P B fallback t K (restore t leaf j w.1)) fuel
        (ControllerPolicyDriver.initial policy N w.2 s₀) := by
  simpa only [entries,trajectory,MarkPolicyReplay.shadow,MarkPolicyReplay.run,restore,restRules,
    ControllerPolicyDriver.selections] using
      ControllerPolicyDriver.schedule_selected policy (markSupplied leaf j)
        (trajectory (n := n) P B fallback t leaf j policy K N s₀) fuel w

theorem visible_covered (K : ℝ) (N fuel : ℕ) (s₀ : (State (t+1) (4096*J^2+1) ell)) (hs : Ready s₀) (hell : 0<ell)
    (w : (RawMarkFactor.Rest d n r J E H t) × Seed) {Z : (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)}
    (hZ : Z ∈ seenPoints (restRules (ell := ell) P B fallback t leaf j K w.1) (leafNode leaf)
      (ControllerOptionalTrajectory.selected (entries (n := n) P B fallback t leaf j policy K N fuel s₀) w) s₀) :
    ∃ i : Fin ((4096*J^2+1)*ell),physicalQuery (n := n) P B fallback t leaf j policy K N fuel s₀ i.val w=Z := by
  have hR : parameterRules (priority t (4096*J^2)) GeometricRepair.target
      (fun w : RawMarkFactor.Rest d n r J E H t × Seed => (restRules (ell := ell) P B fallback t leaf j K w.1).trigger)
      (fun w : RawMarkFactor.Rest d n r J E H t × Seed => (restRules (ell := ell) P B fallback t leaf j K w.1).hit) w=
      restRules (ell := ell) P B fallback t leaf j K w.1 := rfl
  rw [← hR] at hZ
  have h := ControllerVisibleSelections.visible_array_covers
    (Ω := RawMarkFactor.Rest d n r J E H t × Seed)
    (priority t (4096*J^2)) GeometricRepair.target
    (fun w => (restRules (ell := ell) P B fallback t leaf j K w.1).trigger)
    (fun w => (restRules (ell := ell) P B fallback t leaf j K w.1).hit)
    (leafNode leaf) (entries (n := n) P B fallback t leaf j policy K N fuel s₀) (fun _ => s₀) 0 w hs hell hZ
  have hcap : 8^((t+1)-(leafNode leaf).1.val)*(4096*J^2+1)*ell=(4096*J^2+1)*ell := by
    change 8^((t+1)-(t+1))*(4096*J^2+1)*ell=(4096*J^2+1)*ell
    rw [Nat.sub_self,pow_zero,one_mul]
  obtain ⟨q,hq⟩ := h
  refine ⟨⟨q.val,?_⟩,hq⟩
  simpa only [hcap] using q.isLt

theorem repairing_covered (K : ℝ) (N fuel : ℕ) (s₀ : (State (t+1) (4096*J^2+1) ell)) (hs : Ready s₀) (hell : 0<ell)
    (w : (RawMarkFactor.Rest d n r J E H t) × Seed) (i : ℕ) (hi : i≤fuel) (remaining : ℕ) (a : S) (output : Bool)
    (p : Pending (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)) (s : (State (t+1) (4096*J^2+1) ell))
    (hp : trajectory (n := n) P B fallback t leaf j policy K N s₀ i w=.pending remaining a output (.repairing p s))
    (hv : Visible (TaskState.retired s) (leafNode leaf)) :
    ∃ q : Fin ((4096*J^2+1)*ell),query (n := n) P B fallback t leaf j policy K N fuel s₀ w q=
      BoundedNumericalTest.test (numericalProjection t p.point) := by
  have hm := ControllerPolicyTraceInvariant.repairing_visible_mem policy
    (restRules (ell := ell) P B fallback t leaf j K w.1) (markSupplied leaf j)
    (MarkPolicyReplay.ordinary P B fallback t K (restore t leaf j w.1))
    (MarkPolicyReplay.rich P B fallback t K (restore t leaf j w.1))
    N w.2 s₀ i fuel hi remaining a output p s (leafNode leaf) hp hv
  rw [← entries_selected (n := n) P B fallback t leaf j policy K N fuel s₀ w] at hm
  obtain ⟨q,hq⟩ := visible_covered (n := n) P B fallback t leaf j policy K N fuel s₀ hs hell w hm
  exact ⟨q,by rw [query,hq]⟩

end GradientHessian.MarkVisibleQueries
