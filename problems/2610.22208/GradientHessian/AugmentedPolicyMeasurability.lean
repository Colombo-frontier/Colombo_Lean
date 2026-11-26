import GradientHessian.AugmentedPolicyReplay

/-! Joint measurability of augmented executions, including initialization
from the raw-dependent public packet, and of their external-factor shadows. -/

noncomputable section
namespace GradientHessian.AugmentedPolicy
open Classical HigherHierarchy RawHierarchy FrontierState TaskState GeometricRepair
  ComparisonController ComparisonControllerReplay ControllerMeasurable AugmentedDisclosure

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable [∀ t,MeasurableSpace (DirectionPolicyReplay.Point d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Rich d J E H t)]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) [BorelSpace (DirectionPolicyReplay.Point d J E H t)]
  [BorelSpace (DirectionPolicyReplay.Ordinary d J E H t)] [BorelSpace (DirectionPolicyReplay.Rich d J E H t)]
  (policy : Machine.Policy (Seed × Packet d J E H t ell) S (DirectionPolicyReplay.Point d J E H t)
    (Ordinary d J E H t ell) (Rich d J E H t ell))
  (blocked : Action t (4096*J^2) → Bool) (stop : State (t+1) (4096*J^2+1) ell → Bool)

theorem guard_measurable (K : ℝ) :
    Measurable (fun q : Raw d n r J E H t × Phase (t+1) (4096*J^2+1) ell
        (DirectionPolicyReplay.Point d J E H t) (Action t (4096*J^2)) =>
      guardedTick (suppress (rules K (assemble P B fallback t q.1)) blocked) stop q.2) := by
  apply guardedTick_joint_measurable (priority t (4096*J^2)) GeometricRepair.target
    (fun raw s Z a => if blocked a then false else trigger K (assemble P B fallback t raw) s Z a)
    (fun raw => hit (assemble P B fallback t raw))
  · intro s a
    cases hb : blocked a with
    | true => simpa only [hb,if_true] using (measurable_const (a := false) :
        Measurable (fun _ : Raw d n r J E H t × DirectionPolicyReplay.Point d J E H t => false))
    | false => simpa only [hb,Bool.false_eq_true,if_false] using trigger_fixed_joint_measurable P B fallback t K s a
  · exact hit_fixed_joint_measurable P B fallback t

theorem run_joint_measurable {K : ℝ} (hK : 0<K) (fuel : ℕ) :
    Measurable (fun q : Raw d n r J E H t × ControllerPolicyDriver.Config (t+1) (4096*J^2+1) ell S
        (DirectionPolicyReplay.Point d J E H t) (Action t (4096*J^2)) =>
      run P B fallback t policy K blocked stop q.1 fuel q.2) :=
  ControllerPolicyDriver.run_joint_measurable policy
    (fun raw => suppress (rules K (assemble P B fallback t raw)) blocked) stop
    (ordinary P B fallback K t) (rich P B fallback K t)
    (guard_measurable P B fallback t blocked stop K)
    (ordinary_fixed_measurable P B fallback t hK) (rich_fixed_measurable P B fallback t hK) fuel

theorem initial_measurable (K : ℝ) (N : ℕ) (s : State (t+1) (4096*J^2+1) ell) :
    Measurable (fun q : Raw d n r J E H t × Seed => initial P B fallback t policy K q.1 N q.2 s) := by
  have hseed : Measurable (fun q : Raw d n r J E H t × Seed => (q.2,view K (assemble P B fallback t q.1) s)) :=
    measurable_snd.prodMk ((view_fixed_measurable P B fallback t K s).comp measurable_fst)
  exact (ControllerPolicyDriver.initial_measurable (A := Action t (4096*J^2)) policy N s).comp hseed

theorem trajectory_measurable {K : ℝ} (hK : 0<K) (N : ℕ)
    (s : State (t+1) (4096*J^2+1) ell) (fuel : ℕ) :
    Measurable (trajectory (n := n) P B fallback t policy K blocked stop N s fuel) := by
  let C := ControllerPolicyDriver.Config (t+1) (4096*J^2+1) ell S
    (DirectionPolicyReplay.Point d J E H t) (Action t (4096*J^2))
  have hrun : Measurable (fun q : Raw d n r J E H t × C => run P B fallback t policy K blocked stop q.1 fuel q.2) :=
    run_joint_measurable P B fallback t policy blocked stop hK fuel
  have hi : Measurable (fun q : Raw d n r J E H t × Seed => initial P B fallback t policy K q.1 N q.2 s) :=
    initial_measurable P B fallback t policy K N s
  have hm : Measurable (fun q : Raw d n r J E H t × Seed => (q.1,initial P B fallback t policy K q.1 N q.2 s)) :=
    (measurable_fst : Measurable (Prod.fst : Raw d n r J E H t × Seed → Raw d n r J E H t)).prodMk hi
  simpa only [trajectory,Function.comp_def] using hrun.comp hm

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]

def shadowTrajectory (e : Raw d n r J E H t ≃ᵐ V × W) (replacement : V)
    (K : ℝ) (N : ℕ) (s : State (t+1) (4096*J^2+1) ell) (fuel : ℕ) (q : W × Seed) :=
  trajectory P B fallback t policy K blocked stop N s fuel (e.symm (replacement,q.1),q.2)

theorem shadowTrajectory_measurable (e : Raw d n r J E H t ≃ᵐ V × W) (replacement : V)
    {K : ℝ} (hK : 0<K) (N : ℕ) (s : State (t+1) (4096*J^2+1) ell) (fuel : ℕ) :
    Measurable (shadowTrajectory P B fallback t policy blocked stop e replacement K N s fuel) :=
  (trajectory_measurable P B fallback t policy blocked stop hK N s fuel).comp
    ((e.symm.measurable.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)

end GradientHessian.AugmentedPolicy
