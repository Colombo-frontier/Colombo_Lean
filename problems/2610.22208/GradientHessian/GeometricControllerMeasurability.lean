import GradientHessian.GeometricRepairMeasurability
import GradientHessian.ControllerMeasurablePhases

/-! Joint measurability of the actual presampled geometric controller,
including its atomic receipt, internal phases and guarded replay. No
good-event, valid-coefficient, or unit-vector premise is used. -/

noncomputable section
namespace GradientHessian.GeometricRepair
open Classical Matrix LowRank HigherHierarchy TaskState ComparisonController
  ComparisonControllerPhases ComparisonControllerReplay ControllerMeasurable

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h, NormedAddCommGroup (H h)] [∀ h, InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h, MeasurableSpace (H h)] [∀ h, BorelSpace (H h)] [∀ h, FiniteDimensional ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (K : ℝ)
  [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]

theorem actual_choose_joint_measurable :
    Measurable (fun q : (RawHierarchy.Raw d n r J E H t ×
        Pending (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)) ×
          State (t+1) (4096*J^2+1) ell =>
      choose (rules K (RawHierarchy.assemble P B fallback t q.1.1)) q.1.2 q.2) :=
  measurable_from_prod_countable (fun s =>
    choose_fixed_measurable (priority t (4096*J^2)) target
      (fun x => trigger K (RawHierarchy.assemble P B fallback t x))
      (fun x => hit (RawHierarchy.assemble P B fallback t x))
      (trigger_fixed_joint_measurable P B fallback t K) s)

theorem actual_repairRun_joint_measurable (fuel : ℕ) :
    Measurable (fun q : (RawHierarchy.Raw d n r J E H t ×
        Pending (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)) ×
          State (t+1) (4096*J^2+1) ell =>
      repairRun (rules K (RawHierarchy.assemble P B fallback t q.1.1)) q.1.2 fuel q.2) :=
  repairRun_joint_measurable (priority t (4096*J^2)) target
    (fun x => trigger K (RawHierarchy.assemble P B fallback t x))
    (fun x => hit (RawHierarchy.assemble P B fallback t x))
    (trigger_fixed_joint_measurable P B fallback t K) fuel

theorem actual_serve_joint_measurable :
    Measurable (fun q : (RawHierarchy.Raw d n r J E H t ×
        Pending (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)) ×
          State (t+1) (4096*J^2+1) ell =>
      serve (rules K (RawHierarchy.assemble P B fallback t q.1.1)) q.1.2 q.2) :=
  serve_joint_measurable (priority t (4096*J^2)) target
    (fun x => trigger K (RawHierarchy.assemble P B fallback t x))
    (fun x => hit (RawHierarchy.assemble P B fallback t x))
    (trigger_fixed_joint_measurable P B fallback t K)
    (hit_fixed_joint_measurable P B fallback t)

theorem actual_tick_joint_measurable :
    Measurable (fun q : RawHierarchy.Raw d n r J E H t ×
        Phase (t+1) (4096*J^2+1) ell
          (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Action t (4096*J^2)) =>
      tick (rules K (RawHierarchy.assemble P B fallback t q.1)) q.2) :=
  tick_joint_measurable (priority t (4096*J^2)) target
    (fun x => trigger K (RawHierarchy.assemble P B fallback t x))
    (fun x => hit (RawHierarchy.assemble P B fallback t x))
    (trigger_fixed_joint_measurable P B fallback t K)
    (hit_fixed_joint_measurable P B fallback t)

theorem actual_ticks_joint_measurable (fuel : ℕ) :
    Measurable (fun q : RawHierarchy.Raw d n r J E H t ×
        Phase (t+1) (4096*J^2+1) ell
          (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Action t (4096*J^2)) =>
      ticks (rules K (RawHierarchy.assemble P B fallback t q.1)) fuel q.2) :=
  ticks_joint_measurable (priority t (4096*J^2)) target
    (fun x => trigger K (RawHierarchy.assemble P B fallback t x))
    (fun x => hit (RawHierarchy.assemble P B fallback t x))
    (trigger_fixed_joint_measurable P B fallback t K)
    (hit_fixed_joint_measurable P B fallback t) fuel

theorem actual_guardedRun_joint_measurable (stop : State (t+1) (4096*J^2+1) ell → Bool)
    (fuel : ℕ) :
    Measurable (fun q : RawHierarchy.Raw d n r J E H t ×
        Phase (t+1) (4096*J^2+1) ell
          (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Action t (4096*J^2)) =>
      guardedRun (rules K (RawHierarchy.assemble P B fallback t q.1)) stop fuel q.2) :=
  guardedRun_joint_measurable (priority t (4096*J^2)) target
    (fun x => trigger K (RawHierarchy.assemble P B fallback t x))
    (fun x => hit (RawHierarchy.assemble P B fallback t x))
    (trigger_fixed_joint_measurable P B fallback t K)
    (hit_fixed_joint_measurable P B fallback t) stop fuel

end GradientHessian.GeometricRepair
