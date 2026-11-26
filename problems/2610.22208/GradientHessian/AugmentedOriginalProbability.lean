import GradientHessian.AugmentedDirectionProbability
import GradientHessian.AugmentedMarkProbability

/-! Original true-jet policy repair probabilities for all three direction
families, under the actual presampled raw law and independent private seed.
The source validity event, first-hit replay, and finite visibility bound are
proved ingredients rather than caller-supplied stopped-event estimates. -/

noncomputable section
namespace GradientHessian.AugmentedDirectionFamilies
open Classical MeasureTheory Matrix LowRank HigherHierarchy HierarchyAddresses RawHierarchy
  FrontierState TaskState TaskSlots GeometricRepair ComparisonController ComparisonControllerReplay
  RawDirection AugmentedPolicy AugmentedVisibleQueries
open DirectionPolicyReplay (Point centerStop oldStop)

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
variable [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)]
variable (σ : Measure Seed) [IsProbabilityMeasure σ]

def originalRepair (t : ℕ) (a : Action t (4096*J^2))
    (policy : Machine.Policy (Seed × Packet d J E H t ell) S (Point d J E H t) (Ordinary d J E H t ell) (Rich d J E H t ell))
    (K : ℝ) (N : ℕ) (w : Raw d n r J E H t × Seed) : Prop :=
  a ∈ ControllerRepairEvents.actions (rules (ell := ell) K (assemble P B fallback t w.1))
    (selectedPoints P B fallback t policy K N TaskState.initial w) TaskState.initial

theorem original_probability_le_shadow [Nontrivial E] [∀ h,Nontrivial (H h)] [NeZero r]
    (t : ℕ) (a : Action t (4096*J^2)) (target : Slot J t) (ha : directionSlot a=some target)
    (policy : Machine.Policy (Seed × Packet d J E H t ell) S (Point d J E H t) (Ordinary d J E H t ell) (Rich d J E H t ell))
    (hJ : 4≤J) (hP : IsOrthogonalProjector P) (hB : Bᵀ*B=1) (hPB : P*B=B)
    {K : ℝ} (hK : 0<K) (N : ℕ) (hell : 0<ell) :
    ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P t).prod σ).real
      {w | originalRepair (ell := ell) P B fallback t a policy K N w} ≤
    ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P t).prod σ).real
      {w | hitBy P B fallback t (blockDirection target) (actionStop (ell := ell) a) policy K N
        ((N+1)*(8^(t+1)+4)) TaskState.initial w} := by
  letI := RawHierarchy.law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P t
  have hstop : disclosureStop (ell := ell) a=actionStop a := by
    cases a <;> simp only [disclosureStop]
    change none=some target at ha
    cases ha
  apply measureReal_mono
  · intro w hw
    have h := action_hitBy P B fallback t policy K N TaskState.initial (initial_ready hell) hell w a
      (blockDirection target) (by simp only [blockDirection,ha,decide_true]) hw
    simpa only [hstop] using h
  · finiteness

theorem center_original_probability [Nontrivial E] [∀ h,Nontrivial (H h)] [NeZero r]
    (h depth : ℕ) (w : Word depth) (i : Fin 8)
    (policy : Machine.Policy (Seed × Packet d J E H (h+1+depth) ell) S (Point d J E H (h+1+depth))
      (Ordinary d J E H (h+1+depth) ell) (Rich d J E H (h+1+depth) ell))
    (hJ : 4≤J) (hP : IsOrthogonalProjector P) (hB : Bᵀ*B=1) (hPB : P*B=B)
    (hdim : 2≤Module.finrank ℝ (H h)) {K : ℝ} (hK : 16≤K) (N : ℕ) (hell : 0<ell) :
    ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P (h+1+depth)).prod σ).real
      {x | originalRepair (ell := ell) P B fallback (h+1+depth) (centerFactorAction h depth w i) policy K N x} ≤
        (8^(h+2)*(4096*J^2+1)*ell : ℕ)*
          (2*(6*width (4096*J^2) h/radius (4096*J^2) K h)^(Module.finrank ℝ (H h)-1)) := by
  have hm := original_probability_le_shadow (n := n) (ell := ell) P B fallback σ (h+1+depth) (centerFactorAction h depth w i)
    (embed (h+1) depth w (.inr i)) (centerFactorAction_slot h depth w i) policy hJ hP hB hPB (by linarith : 0<K) N hell
  rw [centerFactorAction_stop] at hm
  exact hm.trans (center_shadow_probability P B fallback σ h depth w i policy hdim hK N
    ((N+1)*(8^(h+1+depth+1)+4)) TaskState.initial (initial_ready hell) hell)

theorem old_original_probability [Nontrivial E] [∀ h,Nontrivial (H h)] [NeZero r]
    (depth : ℕ) (w : Word depth) (i : Fin 8) (j : Fin (FirstHeight.depth (4096*J^2+1)+2))
    (policy : Machine.Policy (Seed × Packet d J E H (0+depth) ell) S (Point d J E H (0+depth))
      (Ordinary d J E H (0+depth) ell) (Rich d J E H (0+depth) ell))
    (hJ : 4≤J) (hP : IsOrthogonalProjector P) (hB : Bᵀ*B=1) (hPB : P*B=B)
    {K : ℝ} (hK : 0<K) (N : ℕ) (hell : 0<ell) :
    ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P (0+depth)).prod σ).real
      {x | originalRepair (ell := ell) P B fallback (0+depth) (oldFactorAction depth w i j) policy K N x} ≤
        (8*(4096*J^2+1)*ell : ℕ)*(2*Real.exp (-(Module.finrank ℝ E:ℝ)/18432)) := by
  have hm := original_probability_le_shadow (n := n) (ell := ell) P B fallback σ (0+depth) (oldFactorAction depth w i j)
    (embed 0 depth w (.inl (i,j))) (oldFactorAction_slot depth w i j) policy hJ hP hB hPB hK N hell
  rw [oldFactorAction_stop] at hm
  exact hm.trans (old_shadow_probability P B fallback σ depth w i j policy hK N
    ((N+1)*(8^(0+depth+1)+4)) TaskState.initial (initial_ready hell) hell)

theorem inner_original_probability [Nontrivial E] [∀ h,Nontrivial (H h)] [NeZero r]
    (depth : ℕ) (w : Word depth) (i : Fin 8) (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2))
    (policy : Machine.Policy (Seed × Packet d J E H (0+depth) ell) S (Point d J E H (0+depth))
      (Ordinary d J E H (0+depth) ell) (Rich d J E H (0+depth) ell))
    (hJ : 4≤J) (hP : IsOrthogonalProjector P) (hB : Bᵀ*B=1) (hPB : P*B=B)
    {K : ℝ} (hK : 0<K) (N : ℕ) (hell : 0<ell) :
    ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P (0+depth)).prod σ).real
      {x | originalRepair (ell := ell) P B fallback (0+depth) (innerFactorAction depth w i j k) policy K N x} ≤
        ((4096*J^2+1)*ell : ℕ)*(2*Real.exp (-(Module.finrank ℝ E:ℝ)/18432)) := by
  have hm := original_probability_le_shadow (n := n) (ell := ell) P B fallback σ (0+depth) (innerFactorAction depth w i j k)
    (embed 0 depth w (.inr (i,j,k))) (innerFactorAction_slot depth w i j k) policy hJ hP hB hPB hK N hell
  exact hm.trans (inner_shadow_probability P B fallback σ depth w i j k policy hK N
    ((N+1)*(8^(0+depth+1)+4)) TaskState.initial (initial_ready hell) hell)

end GradientHessian.AugmentedDirectionFamilies


