import GradientHessian.GeometricRawReadouts
import GradientHessian.ControllerMeasurableTypes

/-! The literal repaired controller has measurable raw-dependent tests.
All state and action cases are finite; no geometric validity or good-event
hypothesis enters these all-input measurability statements. -/

noncomputable section
namespace GradientHessian.GeometricRepair
open Classical Matrix LowRank HigherHierarchy ControllerMeasurable TaskState

instance actionMeasurable (t m : ℕ) : MeasurableSpace (Action t m) := ⊤
instance actionSingleton (t m : ℕ) : MeasurableSingletonClass (Action t m) := ⟨fun _ => trivial⟩

theorem measurable_decide_pred {Ω : Type*} [MeasurableSpace Ω] (p : Ω → Prop) [DecidablePred p]
    (hp : MeasurableSet {x | p x}) : Measurable (fun x => decide (p x)) := by
  convert Measurable.ite hp (measurable_const (a := true)) (measurable_const (a := false)) using 1

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h, NormedAddCommGroup (H h)] [∀ h, InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h, MeasurableSpace (H h)] [∀ h, BorelSpace (H h)] [∀ h, FiniteDimensional ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ)
  [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]

theorem trigger_fixed_joint_measurable (K : ℝ) (s : State (t+1) (4096*J^2+1) ell)
    (a : Action t (4096*J^2)) :
    Measurable (fun p : RawHierarchy.Raw d n r J E H t ×
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
      trigger K (RawHierarchy.assemble P B fallback t p.1) s p.2 a) := by
  cases a with
  | localized h path i =>
    simp only [trigger]
    apply measurable_decide_pred
    exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
      (measurableSet_le (localDistance_joint_measurable P B fallback t K h path i) measurable_const))
  | old path i j =>
    simp only [trigger]
    apply measurable_decide_pred
    exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
      (measurableSet_lt measurable_const (oldReadout_joint_measurable P B fallback t path i j).abs))
  | inner leaf task j =>
    simp only [trigger]
    apply measurable_decide_pred
    exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
      (measurableSet_lt measurable_const (innerReadout_joint_measurable P B fallback t leaf task j).abs))
  | futureMark leaf task =>
    simp only [trigger]
    apply measurable_decide_pred
    exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
      (measurableSet_lt measurable_const (markReadout_joint_measurable P B fallback t leaf task).abs))

theorem hit_fixed_joint_measurable (s : State (t+1) (4096*J^2+1) ell) :
    Measurable (fun p : RawHierarchy.Raw d n r J E H t ×
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
      hit (RawHierarchy.assemble P B fallback t p.1) s p.2) := by
  cases hc : TaskState.current s with
  | none =>
    have he : (fun p : RawHierarchy.Raw d n r J E H t ×
        Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
        hit (RawHierarchy.assemble P B fallback t p.1) s p.2) = fun _ => false := by
      funext p
      unfold hit
      split <;> simp_all
    rw [he]
    exact measurable_const
  | some leaf =>
    simp_rw [hit_current _ s _ hc]
    exact measurable_decide_pred _ (measurableSet_lt measurable_const
      (markReadout_joint_measurable P B fallback t leaf ⟨(s.completed leaf).val,current_live s hc⟩).abs)

theorem trigger_joint_measurable (K : ℝ) :
    Measurable (fun p : (RawHierarchy.Raw d n r J E H t ×
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) ×
        (State (t+1) (4096*J^2+1) ell × Action t (4096*J^2)) =>
      trigger K (RawHierarchy.assemble P B fallback t p.1.1) p.2.1 p.1.2 p.2.2) :=
  measurable_from_prod_countable (fun sa => trigger_fixed_joint_measurable P B fallback t K sa.1 sa.2)

theorem hit_joint_measurable :
    Measurable (fun p : (RawHierarchy.Raw d n r J E H t ×
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) × State (t+1) (4096*J^2+1) ell =>
      hit (RawHierarchy.assemble P B fallback t p.1.1) p.2 p.1.2) :=
  measurable_from_prod_countable (hit_fixed_joint_measurable P B fallback t)

end GradientHessian.GeometricRepair
