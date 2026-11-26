import GradientHessian.AugmentedActionProbability
import GradientHessian.AugmentedRepairMeasurability
import GradientHessian.RepairHeightAggregation

/-! The source repair-cost expectation for augmented comparison policies.
All four per-action bounds are proved from actual censored executions and
the original raw product law; dimensions are the literal source allocation. -/

noncomputable section
namespace GradientHessian.AugmentedRepairCost
open Classical MeasureTheory Matrix LowRank HigherHierarchy HierarchyAddresses RawHierarchy
  FrontierState TaskState TaskSlots GeometricRepair ComparisonController ComparisonControllerReplay
  AugmentedPolicy AugmentedDirectionFamilies RepairHeightAggregation
open DirectionPolicyReplay (Point)
open AllocationParameters Allocation RepairAllocation

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)] [∀ h,Nontrivial (H h)]
variable [∀ t,MeasurableSpace (Point d J E H t)] [∀ t,BorelSpace (Point d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Ordinary d J E H t)] [∀ t,BorelSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Rich d J E H t)] [∀ t,BorelSpace (DirectionPolicyReplay.Rich d J E H t)]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
variable [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] [NeZero r]
variable (σ : Measure Seed) [IsProbabilityMeasure σ]
variable (t : ℕ) (policy : Machine.Policy (Seed × Packet d J E H t ell) S (Point d J E H t) (Ordinary d J E H t ell) (Rich d J E H t ell))

theorem source_family_probability (Cp : ℝ)
    (hE : Module.finrank ℝ E=lowDimension Cp (4096*J^2+1))
    (hH : ∀ h,Module.finrank ℝ (H h)=levelDimension (lowDimension Cp (4096*J^2+1)) (cutoff (4096*J^2+1)) (h+2))
    (hJ : 4≤J) (hP : IsOrthogonalProjector P) (hB : Bᵀ*B=1) (hPB : P*B=B)
    {K : ℝ} (hK : 16≤K) (N : ℕ) (hell : 0<ell) (a : Action t (4096*J^2)) :
    ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P t).prod σ).real
      {w | originalRepair (ell := ell) P B fallback t a policy K N w} ≤
        familyBound (fun h => localizedBound K Cp (4096*J^2+1) ell h.val)
          (oldBound Cp (4096*J^2+1) ell) (innerBound Cp (4096*J^2+1) ell) (markBound (4096*J^2+1) ell r) a := by
  have hK0 : 0<K := by linarith
  cases a with
  | localized h path i =>
    have hd : 2≤Module.finrank ℝ (H h.val) := by
      rw [hH]
      unfold levelDimension
      split_ifs
      · exact (by norm_num : 2≤8).trans (lowDimension_ge_eight Cp _)
      · norm_num
    have hb := localized_action_probability (n := n) (ell := ell) P B fallback σ t policy h path i hJ hP hB hPB hd hK N hell
    apply hb.trans_eq
    have hr : 6*width (4096*J^2) h.val/radius (4096*J^2) K h.val=6/(K*2^h.val) := by
      rw [radius_eq_width]
      exact mul_div_mul_right 6 (K*2^h.val) (width_pos (4096*J^2) h.val).ne'
    rw [hr,hH]
    simp only [familyBound,localizedBound,levelCost,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    ring
  | old path i j =>
    have hb := old_action_probability (n := n) (ell := ell) P B fallback σ t policy path i j hJ hP hB hPB hK0 N hell
    apply hb.trans_eq
    simp only [familyBound,oldBound,memoryDecay,hE,Nat.cast_mul,Nat.cast_ofNat]
    ring
  | inner leaf j k =>
    have hb := inner_action_probability (n := n) (ell := ell) P B fallback σ t policy leaf j k hJ hP hB hPB hK0 N hell
    apply hb.trans_eq
    simp only [familyBound,innerBound,memoryDecay,hE,Nat.cast_mul,Nat.cast_ofNat]
    ring
  | futureMark leaf j =>
    have hb := mark_action_probability (n := n) (ell := ell) P B fallback σ t policy leaf j hJ hP hB hPB hK0 N hell
    apply hb.trans_eq
    simp only [familyBound,markBound,Nat.cast_mul]
    have he : -(1/8:ℝ)*(1/3072)^2*(r:ℝ)=-(r:ℝ)/75497472 := by ring
    rw [he]
    ring

theorem expected_repair_cost (Cp : ℝ)
    (hE : Module.finrank ℝ E=lowDimension Cp (4096*J^2+1))
    (hH : ∀ h,Module.finrank ℝ (H h)=levelDimension (lowDimension Cp (4096*J^2+1)) (cutoff (4096*J^2+1)) (h+2))
    (hJ : 4≤J) (hP : IsOrthogonalProjector P) (hB : Bᵀ*B=1) (hPB : P*B=B)
    {K : ℝ} (hK : 384≤K) (hCp : lowAllocation≤Cp)
    (hr : markAllocation*((4096*J^2+1:ℕ):ℝ)≤r) (N : ℕ) (hell : 0<ell) (hellM : ell≤4096*J^2+1) :
    (∫ w, (AugmentedPolicy.repairCount (ell := ell) P B fallback t policy K N w : ℝ)
      ∂((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P t).prod σ)) ≤
        (8:ℝ)^(t+1)*(4096*(J:ℝ)^2+1)/256 := by
  letI := RawHierarchy.law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P t
  have hK0 : 0<K := by linarith
  have hb := ControllerRepairProbability.mean_le_probability_bounds
    ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P t).prod σ)
    (actualRules (ell := ell) P B fallback t K)
    (selectedPoints P B fallback t policy K N TaskState.initial) (fun _ => TaskState.initial)
    (fun _ => initial_ready hell) hell publicCost (fun _ _ => le_rfl)
    (repairCount_measurable P B fallback t policy hK0 N)
    (repairEvent_measurable P B fallback t policy hK0 N)
    (familyBound (fun h => localizedBound K Cp (4096*J^2+1) ell h.val)
      (oldBound Cp (4096*J^2+1) ell) (innerBound Cp (4096*J^2+1) ell) (markBound (4096*J^2+1) ell r))
    (source_family_probability (n := n) (ell := ell) P B fallback σ t policy Cp hE hH hJ hP hB hPB (by linarith) N hell)
  exact hb.trans (by simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using family_cost_bound hK hCp hellM hr t)

end GradientHessian.AugmentedRepairCost

