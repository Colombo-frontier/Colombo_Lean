import GradientHessian.AugmentedEarlyPhase
import GradientHessian.AugmentedRepairMeasurability
import GradientHessian.ControllerAdaptiveTally

noncomputable section
namespace GradientHessian.AugmentedEarlyPhase
open Classical MeasureTheory HigherHierarchy RawHierarchy FrontierState TaskState TaskSlots
  GeometricRepair ComparisonController ComparisonControllerLedger ControllerMeasurable AugmentedDisclosure AugmentedPolicy
open DirectionPolicyReplay (Point)
open scoped BigOperators

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

theorem earlyEvent_measurable {K : ℝ} (hK : 0<K) (N : ℕ)
    (leaf : Leaf (t+1)) (j : Fin (4096*J^2+1)) :
    MeasurableSet (earlyEvent (n := n) P B fallback t policy K N leaf j) := by
  have h := ControllerAdaptiveExecution.adaptive_task_count_measurable
    (priority t (4096*J^2)) GeometricRepair.target
    (fun q : Raw d n r J E H t × Seed => trigger (ell := ell) K (assemble P B fallback t q.1))
    (fun q : Raw d n r J E H t × Seed => hit (ell := ell) (assemble P B fallback t q.1))
    (AugmentedPolicy.seed_trigger_measurable (Seed := Seed) P B fallback t K)
    (AugmentedPolicy.seed_hit_measurable (Seed := Seed) P B fallback t)
    policy (fun q => AugmentedPolicy.ordinary P B fallback K t q.1)
    (fun q => AugmentedPolicy.rich P B fallback K t q.1)
    (AugmentedPolicy.seed_ordinary_measurable (Seed := Seed) P B fallback t hK)
    (AugmentedPolicy.seed_rich_measurable (Seed := Seed) P B fallback t hK)
    N _ (AugmentedPolicy.initialAlgorithm_measurable P B fallback t policy K)
    (fun _ => TaskState.initial) measurable_const (leaf,j)
  exact measurableSet_lt measurable_const h

theorem early_mean_eq_probability_sum (μ : Measure (Raw d n r J E H t × Seed)) [IsFiniteMeasure μ]
    {K : ℝ} (hK : 0<K) (N : ℕ) (hell : 0<ell) :
    (∫ w,(earlyCount P B fallback t policy K N w : ℝ) ∂μ)=
      ∑ q : ControllerEarlyEvents.Task (t+1) (4096*J^2+1),μ.real (earlyEvent P B fallback t policy K N q.1 q.2) := by
  have hi (q : ControllerEarlyEvents.Task (t+1) (4096*J^2+1)) :
      Integrable ((earlyEvent P B fallback t policy K N q.1 q.2).indicator (fun _ => (1:ℝ))) μ :=
    (integrable_const _).indicator (earlyEvent_measurable P B fallback t policy hK N q.1 q.2)
  calc
    _ = ∫ w, ∑ q : ControllerEarlyEvents.Task (t+1) (4096*J^2+1),
        (earlyEvent P B fallback t policy K N q.1 q.2).indicator (fun _ => (1:ℝ)) w ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with w
      have he := ControllerEarlyEvents.early_eq_event_sum
        (rules (ell := ell) K (assemble P B fallback t w.1))
        (AugmentedPolicy.selectedPoints P B fallback t policy K N TaskState.initial w)
        (initial_ready hell) hell
      have he' := congrArg (fun k : ℕ => (k:ℝ)) he
      simpa only [earlyCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
        earlyEvent,Set.indicator_apply,Set.mem_setOf_eq] using he'
    _ = _ := by
      rw [integral_finset_sum Finset.univ (fun q _ => hi q)]
      apply Finset.sum_congr rfl
      intro q _
      rw [integral_indicator_const _ (earlyEvent_measurable P B fallback t policy hK N q.1 q.2)]
      simp

theorem early_mean_le_inventory_fraction (μ : Measure (Raw d n r J E H t × Seed)) [IsFiniteMeasure μ]
    {K : ℝ} (hK : 0<K) (N : ℕ) (hell : 0<ell)
    (hp : ∀ (leaf : Leaf (t+1)) (j : Fin (4096*J^2+1)),
      μ.real (earlyEvent P B fallback t policy K N leaf j)≤1/256) :
    (∫ w,(earlyCount P B fallback t policy K N w : ℝ) ∂μ)≤
      (8:ℝ)^(t+1)*(4096*J^2+1)/256 := by
  rw [early_mean_eq_probability_sum P B fallback t policy μ hK N hell]
  have hm := Finset.sum_le_sum (s := Finset.univ)
    (fun (q : ControllerEarlyEvents.Task (t+1) (4096*J^2+1)) _ => hp q.1 q.2)
  simpa only [Finset.sum_const,Finset.card_univ,ControllerEarlyEvents.Task,
    Fintype.card_prod,FrontierState.leaf_card,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,mul_one_div] using hm

end GradientHessian.AugmentedEarlyPhase
