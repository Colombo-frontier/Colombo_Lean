import GradientHessian.ControllerAdaptiveLedger
import GradientHessian.AugmentedEarlyExpectation
import GradientHessian.AugmentedRepairMeasurability
import GradientHessian.Ledger

/-! Probability accounting for the literal augmented comparison oracle.
The policy reads the full initial packet before selecting its first point.
Both expectation estimates remain explicit only in this intermediate
assembly theorem; geometry, output accounting and integrability are proved. -/

noncomputable section
namespace GradientHessian.AugmentedLedger
open Classical MeasureTheory HigherHierarchy RawHierarchy FrontierState TaskState TaskSlots
  GeometricRepair ComparisonController ComparisonControllerLedger AugmentedDisclosure AugmentedPolicy
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

def output (K : ℝ) (N : ℕ) (w : Raw d n r J E H t × Seed) : Point d J E H t :=
  ControllerAdaptiveExecution.output policy (rules K (assemble P B fallback t w.1))
    (AugmentedPolicy.ordinary P B fallback K t w.1) (AugmentedPolicy.rich P B fallback K t w.1)
    N (policy.initial (w.2,view K (assemble P B fallback t w.1) TaskState.initial)) TaskState.initial

def Caps (K : ℝ) (G Hcap : ℕ) (w : Raw d n r J E H t × Seed) : Prop :=
  ControllerAdaptiveExecution.HasCaps policy (rules K (assemble P B fallback t w.1))
    (AugmentedPolicy.ordinary P B fallback K t w.1) (AugmentedPolicy.rich P B fallback K t w.1)
    (policy.initial (w.2,view K (assemble P B fallback t w.1) TaskState.initial)) TaskState.initial G Hcap

theorem early_integrable (μ : Measure (Raw d n r J E H t × Seed)) [IsFiniteMeasure μ]
    {K : ℝ} (hK : 0<K) (N : ℕ) (hell : 0<ell) :
    Integrable (fun w => (AugmentedEarlyPhase.earlyCount P B fallback t policy K N w:ℝ)) μ := by
  let ev := AugmentedEarlyPhase.earlyEvent (n := n) P B fallback t policy K N
  have hi (q : ControllerEarlyEvents.Task (t+1) (4096*J^2+1)) :
      Integrable ((ev q.1 q.2).indicator (fun _ => (1:ℝ))) μ :=
    (integrable_const _).indicator (AugmentedEarlyPhase.earlyEvent_measurable P B fallback t policy hK N q.1 q.2)
  have hs := integrable_finset_sum Finset.univ (fun q _ => hi q)
  apply hs.congr
  filter_upwards [] with w
  have he := ControllerEarlyEvents.early_eq_event_sum
    (rules (ell := ell) K (assemble P B fallback t w.1))
    (selectedPoints P B fallback t policy K N TaskState.initial w) (initial_ready hell) hell
  have he' := congrArg (fun k : ℕ => (k:ℝ)) he
  symm
  simpa only [AugmentedEarlyPhase.earlyCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
    ev,AugmentedEarlyPhase.earlyEvent,Set.indicator_apply,Set.mem_setOf_eq] using he'

theorem repair_integrable (μ : Measure (Raw d n r J E H t × Seed)) [IsFiniteMeasure μ]
    {K : ℝ} (hK : 0<K) (N : ℕ) (hell : 0<ell) :
    Integrable (fun w => (AugmentedPolicy.repairCount P B fallback t policy K N w:ℝ)) μ :=
  ControllerRepairProbability.count_integrable μ
    (actualRules (ell := ell) P B fallback t K)
    (selectedPoints P B fallback t policy K N TaskState.initial) (fun _ => TaskState.initial)
    (fun _ => initial_ready hell) hell
    (fun a => (subtree (GeometricRepair.target a)).card*(4096*J^2+1)) (fun _ _ => le_rfl)
    (repairCount_measurable P B fallback t policy hK N)
    (repairEvent_measurable P B fallback t policy hK N)

theorem capped_task_ledger {K : ℝ} (hK : 16≤K) (N G Hcap : ℕ) (hell : 0<ell)
    (w : Raw d n r J E H t × Seed)
    (hd : Valid _ _ _ _ t (assemble P B fallback t w.1))
    (hcaps : Caps P B fallback t policy K G Hcap w)
    (hg : ‖gradient (scalar K t (assemble P B fallback t w.1)) (output P B fallback t policy K N w)‖≤1) :
    8^(t+1)*(4096*J^2+1)≤Hcap*(4096*J^2+1)+(G+1)/ell+
      AugmentedEarlyPhase.earlyCount P B fallback t policy K N w+
      AugmentedPolicy.repairCount P B fallback t policy K N w := by
  exact ControllerAdaptiveExecution.capped_task_ledger hK (assemble P B fallback t w.1) hd policy
    (AugmentedPolicy.ordinary P B fallback K t w.1) (AugmentedPolicy.rich P B fallback K t w.1)
    N (policy.initial (w.2,view K (assemble P B fallback t w.1) TaskState.initial)) hell G Hcap hcaps hg

theorem success_probability (μ : Measure (Raw d n r J E H t × Seed)) [IsProbabilityMeasure μ]
    {K : ℝ} (hK : 16≤K) (N G Hcap : ℕ) (hell : 0<ell)
    (hvalid : ∀ᵐ w ∂μ,Valid _ _ _ _ t (assemble P B fallback t w.1))
    (hcaps : ∀ᵐ w ∂μ,Caps P B fallback t policy K G Hcap w)
    (hrich : (Hcap:ℝ)≤(8:ℝ)^(t+1)/2)
    (hordinary : (G:ℝ)+1≤(8:ℝ)^(t+1)*(4096*J^2+1:ℕ)*ell/4)
    (hearly : (∫ w,(AugmentedEarlyPhase.earlyCount P B fallback t policy K N w:ℝ) ∂μ)≤
      (8:ℝ)^(t+1)*(4096*J^2+1:ℕ)/256)
    (hrepair : (∫ w,(AugmentedPolicy.repairCount P B fallback t policy K N w:ℝ) ∂μ)≤
      (8:ℝ)^(t+1)*(4096*J^2+1:ℕ)/256) :
    μ.real {w | ‖gradient (scalar K t (assemble P B fallback t w.1)) (output P B fallback t policy K N w)‖≤1}≤1/32 := by
  let good : Set (Raw d n r J E H t × Seed) := {w | Valid _ _ _ _ t (assemble P B fallback t w.1) ∧
    Caps P B fallback t policy K G Hcap w ∧
    ‖gradient (scalar K t (assemble P B fallback t w.1)) (output P B fallback t policy K N w)‖≤1}
  have heq : {w | ‖gradient (scalar K t (assemble P B fallback t w.1)) (output P B fallback t policy K N w)‖≤1}=ᵐ[μ]good := by
    filter_upwards [hvalid,hcaps] with w hw hc
    apply propext
    change _ ↔ Valid _ _ _ _ t (assemble P B fallback t w.1) ∧ Caps P B fallback t policy K G Hcap w ∧ _
    simp only [hw,hc,true_and]
    rfl
  rw [measureReal_congr heq]
  apply Ledger.success_probability_le_one_thirty_second μ good
    (fun w => (AugmentedEarlyPhase.earlyCount P B fallback t policy K N w:ℝ))
    (fun w => (AugmentedPolicy.repairCount P B fallback t policy K N w:ℝ))
    (n := (8:ℝ)^(t+1)) (M := ((4096*J^2+1:ℕ):ℝ)) (h := (Hcap:ℝ)) (G := (G:ℝ)) (ell := (ell:ℝ))
    (by positivity) (by positivity) (by exact_mod_cast hell) hrich hordinary
    (fun _ => Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _)
    (early_integrable P B fallback t policy μ (by linarith) N hell)
    (repair_integrable P B fallback t policy μ (by linarith) N hell) hearly hrepair
  intro w hw
  have hb := capped_task_ledger P B fallback t policy hK N G Hcap hell w hw.1 hw.2.1 hw.2.2
  have hb' : (8:ℝ)^(t+1)*(4096*J^2+1:ℕ)≤(Hcap:ℝ)*(4096*J^2+1:ℕ)+(((G+1)/ell:ℕ):ℝ)+
      AugmentedEarlyPhase.earlyCount P B fallback t policy K N w+AugmentedPolicy.repairCount P B fallback t policy K N w := by
    exact_mod_cast hb
  have hd : (((G+1)/ell:ℕ):ℝ)≤((G:ℝ)+1)/ell := by
    simpa only [Nat.cast_add,Nat.cast_one] using (Nat.cast_div_le (α := ℝ) (m := G+1) (n := ell))
  linarith

end GradientHessian.AugmentedLedger
