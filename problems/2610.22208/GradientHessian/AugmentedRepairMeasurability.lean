import GradientHessian.AugmentedPolicyEvents
import GradientHessian.AugmentedPolicyMeasurability
import GradientHessian.ControllerAdaptiveMeasurability
import GradientHessian.ControllerRepairProbability

/-! Actual repair charge and finite-action events of augmented policies
are jointly measurable in the presampled source and independent seed. -/

noncomputable section
namespace GradientHessian.AugmentedPolicy
open Classical HigherHierarchy RawHierarchy FrontierState TaskState GeometricRepair
  ComparisonController ComparisonControllerLedger ControllerMeasurable AugmentedDisclosure
open DirectionPolicyReplay (Point)

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable [∀ t,MeasurableSpace (Point d J E H t)] [∀ t,BorelSpace (Point d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Ordinary d J E H t)] [∀ t,BorelSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Rich d J E H t)] [∀ t,BorelSpace (DirectionPolicyReplay.Rich d J E H t)]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (policy : Machine.Policy (Seed × Packet d J E H t ell) S (Point d J E H t)
    (Ordinary d J E H t ell) (Rich d J E H t ell))

def actualRules (K : ℝ) (q : Raw d n r J E H t × Seed) :
    Rules (t+1) (4096*J^2+1) ell (Point d J E H t) (Action t (4096*J^2)) :=
  rules K (assemble P B fallback t q.1)

def repairCount (K : ℝ) (N : ℕ) (q : Raw d n r J E H t × Seed) : ℕ :=
  ControllerRepairProbability.count (actualRules (ell := ell) P B fallback t K)
    (selectedPoints P B fallback t policy K N TaskState.initial) (fun _ => TaskState.initial) q

def repairEvent (K : ℝ) (N : ℕ) (a : Action t (4096*J^2)) : Set (Raw d n r J E H t × Seed) :=
  ControllerRepairProbability.event (actualRules (ell := ell) P B fallback t K)
    (selectedPoints P B fallback t policy K N TaskState.initial) (fun _ => TaskState.initial) a

theorem initialAlgorithm_measurable (K : ℝ) :
    Measurable (fun q : Raw d n r J E H t × Seed =>
      policy.initial (q.2,view K (assemble P B fallback t q.1) TaskState.initial)) :=
  policy.initial_measurable.comp
    (measurable_snd.prodMk ((view_fixed_measurable P B fallback t K TaskState.initial).comp measurable_fst))

theorem seed_trigger_measurable (K : ℝ) (s : State (t+1) (4096*J^2+1) ell) (a : Action t (4096*J^2)) :
    Measurable (fun q : (Raw d n r J E H t × Seed) × Point d J E H t =>
      trigger K (assemble P B fallback t q.1.1) s q.2 a) := by
  have hm : Measurable (fun q : (Raw d n r J E H t × Seed) × Point d J E H t => (q.1.1,q.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  simpa only [Function.comp_def] using (trigger_fixed_joint_measurable P B fallback t K s a).comp hm

theorem seed_hit_measurable (s : State (t+1) (4096*J^2+1) ell) :
    Measurable (fun q : (Raw d n r J E H t × Seed) × Point d J E H t =>
      hit (assemble P B fallback t q.1.1) s q.2) := by
  have hm : Measurable (fun q : (Raw d n r J E H t × Seed) × Point d J E H t => (q.1.1,q.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  simpa only [Function.comp_def] using (hit_fixed_joint_measurable P B fallback t s).comp hm

theorem seed_ordinary_measurable {K : ℝ} (hK : 0<K) (before after : State (t+1) (4096*J^2+1) ell) :
    Measurable (fun q : (Raw d n r J E H t × Seed) × Point d J E H t => ordinary P B fallback K t q.1.1 before after q.2) := by
  have hm : Measurable (fun q : (Raw d n r J E H t × Seed) × Point d J E H t => (q.1.1,q.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  simpa only [Function.comp_def] using (ordinary_fixed_measurable P B fallback t hK before after).comp hm

theorem seed_rich_measurable {K : ℝ} (hK : 0<K) (before after : State (t+1) (4096*J^2+1) ell) :
    Measurable (fun q : (Raw d n r J E H t × Seed) × Point d J E H t => rich P B fallback K t q.1.1 before after q.2) := by
  have hm : Measurable (fun q : (Raw d n r J E H t × Seed) × Point d J E H t => (q.1.1,q.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  simpa only [Function.comp_def] using (rich_fixed_measurable P B fallback t hK before after).comp hm

theorem repairCount_measurable {K : ℝ} (hK : 0<K) (N : ℕ) :
    Measurable (repairCount (n := n) P B fallback t policy K N) := by
  have h := ControllerAdaptiveExecution.repair_count_measurable (priority t (4096*J^2)) GeometricRepair.target
    (fun q : Raw d n r J E H t × Seed => trigger (ell := ell) K (assemble P B fallback t q.1))
    (fun q : Raw d n r J E H t × Seed => hit (ell := ell) (assemble P B fallback t q.1))
    (seed_trigger_measurable (Seed := Seed) P B fallback t K) (seed_hit_measurable (Seed := Seed) P B fallback t)
    policy (fun q => ordinary P B fallback K t q.1) (fun q => rich P B fallback K t q.1)
    (seed_ordinary_measurable (Seed := Seed) P B fallback t hK) (seed_rich_measurable (Seed := Seed) P B fallback t hK)
    N _ (initialAlgorithm_measurable P B fallback t policy K) (fun _ => TaskState.initial) measurable_const
  exact h

theorem repairEvent_measurable {K : ℝ} (hK : 0<K) (N : ℕ) (a : Action t (4096*J^2)) :
    MeasurableSet (repairEvent (n := n) P B fallback t policy K N a) := by
  have h := ControllerAdaptiveExecution.action_event_measurable (priority t (4096*J^2)) GeometricRepair.target
    (fun q : Raw d n r J E H t × Seed => trigger (ell := ell) K (assemble P B fallback t q.1))
    (fun q : Raw d n r J E H t × Seed => hit (ell := ell) (assemble P B fallback t q.1))
    (seed_trigger_measurable (Seed := Seed) P B fallback t K) (seed_hit_measurable (Seed := Seed) P B fallback t)
    policy (fun q => ordinary P B fallback K t q.1) (fun q => rich P B fallback K t q.1)
    (seed_ordinary_measurable (Seed := Seed) P B fallback t hK) (seed_rich_measurable (Seed := Seed) P B fallback t hK)
    N _ (initialAlgorithm_measurable P B fallback t policy K) (fun _ => TaskState.initial) measurable_const a
  exact h

end GradientHessian.AugmentedPolicy
