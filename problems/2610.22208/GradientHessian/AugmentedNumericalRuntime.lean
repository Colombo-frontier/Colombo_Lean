import GradientHessian.AugmentedNumericalReplies
import GradientHessian.NumericalShadowRules
import GradientHessian.NumericalDriverInstructions

/-! One literal chronological controller transition, parameterized by the
external factor, numerical cache and the single product reply. All runtime
inputs use their original Borel structures; the state counters are finite. -/

noncomputable section
namespace GradientHessian.AugmentedNumericalRuntime
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
variable (policy : Machine.Policy (Seed × AugmentedPolicy.Packet d J E H t ell) S
  (DirectionPolicyReplay.Point d J E H t)
  (AugmentedPolicy.Ordinary d J E H t ell) (AugmentedPolicy.Rich d J E H t ell))
def advance (K : ℝ) (stop : State (t+1) (4096*J^2+1) ell → Bool)
    (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J) (Ay : EuclideanSpace ℝ (Fin d))
    (q : Config (t+1) (4096*J^2+1) ell S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
      (Action t (4096*J^2))) :=
  ControllerPolicyDriver.step policy (NumericalShadowRules.shadowRules P B fallback t leaf K w c) stop
    (fun before after Z => AugmentedNumericalReplies.ordinary P B fallback t leaf K w c before after Z Ay)
    (AugmentedNumericalReplies.rich P B fallback t leaf K w c) q

theorem advance_measurable {K : ℝ} (hK : 0<K)
    (stop : State (t+1) (4096*J^2+1) ell → Bool) :
    Measurable (fun q : ((RawLeafFactor.Rest d n r J E H t × Cache d J) × EuclideanSpace ℝ (Fin d)) ×
      Config (t+1) (4096*J^2+1) ell S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
        (Action t (4096*J^2)) => advance P B fallback t leaf policy K stop q.1.1.1 q.1.1.2 q.1.2 q.2) := by
  let R := fun w : (RawLeafFactor.Rest d n r J E H t × Cache d J) × EuclideanSpace ℝ (Fin d) =>
    NumericalShadowRules.shadowRules (ell := ell) P B fallback t leaf K w.1.1 w.1.2
  have ht : ∀ s a,Measurable (fun q : ((RawLeafFactor.Rest d n r J E H t × Cache d J) ×
      EuclideanSpace ℝ (Fin d)) × Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t => (R q.1).trigger s q.2 a) := by
    intro s a
    have hmap : Measurable (fun q : ((RawLeafFactor.Rest d n r J E H t × Cache d J) ×
        EuclideanSpace ℝ (Fin d)) × Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t => (q.1.1,q.2)) :=
      (measurable_fst.comp measurable_fst).prodMk measurable_snd
    have h := (NumericalShadowRules.shadow_trigger_measurable (n := n) P B fallback t leaf K s a).comp hmap
    simpa only [Function.comp_def,R] using h
  have hh : ∀ s,Measurable (fun q : ((RawLeafFactor.Rest d n r J E H t × Cache d J) ×
      EuclideanSpace ℝ (Fin d)) × Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t => (R q.1).hit s q.2) := by
    intro s
    have hmap : Measurable (fun q : ((RawLeafFactor.Rest d n r J E H t × Cache d J) ×
        EuclideanSpace ℝ (Fin d)) × Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t => (q.1.1,q.2)) :=
      (measurable_fst.comp measurable_fst).prodMk measurable_snd
    have h := (NumericalShadowRules.cached_hit_measurable (n := n) P B fallback t leaf s).comp hmap
    simpa only [Function.comp_def,R,NumericalShadowRules.shadowRules] using h
  have hg : Measurable (fun q : ((RawLeafFactor.Rest d n r J E H t × Cache d J) × EuclideanSpace ℝ (Fin d)) ×
      Phase (t+1) (4096*J^2+1) ell (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Action t (4096*J^2)) =>
      guardedTick (R q.1) stop q.2) := by
    have hbase := guardedTick_joint_measurable (priority t (4096*J^2)) target
      (fun w => (R w).trigger) (fun w => (R w).hit) ht hh stop
    have heR (w : (RawLeafFactor.Rest d n r J E H t × Cache d J) × EuclideanSpace ℝ (Fin d)) :
        parameterRules (priority t (4096*J^2)) target (fun w => (R w).trigger) (fun w => (R w).hit) w=R w := rfl
    simpa only [heR] using hbase
  apply step_joint_measurable policy R stop
    (fun w before after Z => AugmentedNumericalReplies.ordinary P B fallback t leaf K w.1.1 w.1.2 before after Z w.2)
    (fun w => AugmentedNumericalReplies.rich P B fallback t leaf K w.1.1 w.1.2) hg
  · intro before after
    have hmap : Measurable (fun q : ((RawLeafFactor.Rest d n r J E H t × Cache d J) ×
        EuclideanSpace ℝ (Fin d)) × Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
        ((q.1.1,q.2),q.1.2)) :=
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk (measurable_snd.comp measurable_fst)
    have h := (AugmentedNumericalReplies.ordinary_fixed_measurable (n := n) P B fallback t leaf hK before after).comp hmap
    simpa only [Function.comp_def] using h
  · intro before after
    have hmap : Measurable (fun q : ((RawLeafFactor.Rest d n r J E H t × Cache d J) ×
        EuclideanSpace ℝ (Fin d)) × Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
        (q.1.1,q.2)) := (measurable_fst.comp measurable_fst).prodMk measurable_snd
    have h := (AugmentedNumericalReplies.rich_fixed_measurable (n := n) P B fallback t leaf hK before after).comp hmap
    simpa only [Function.comp_def] using h

end GradientHessian.AugmentedNumericalRuntime

