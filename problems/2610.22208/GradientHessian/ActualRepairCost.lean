import GradientHessian.DirectionActionProbability
import GradientHessian.MarkOriginalRepairProbability
import GradientHessian.GeometricPolicyRepair

/-! The source repair-cost expectation for the original true-jet policy.
All four per-action bounds are proved from actual censored executions and
the original raw product law; dimensions are the literal source allocation. -/

noncomputable section
namespace GradientHessian.ActualRepairCost
open Classical MeasureTheory Matrix LowRank HigherHierarchy HierarchyAddresses RawHierarchy
  FrontierState TaskState TaskSlots GeometricRepair ComparisonController ComparisonControllerReplay
  DirectionPolicyReplay DirectionFamilies RepairHeightAggregation AllocationParameters Allocation RepairAllocation

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)] [∀ h,Nontrivial (H h)]
variable [∀ t,MeasurableSpace (Point d J E H t)] [∀ t,BorelSpace (Point d J E H t)]
  [∀ t,MeasurableSpace (Ordinary d J E H t)] [∀ t,BorelSpace (Ordinary d J E H t)]
  [∀ t,MeasurableSpace (Rich d J E H t)] [∀ t,BorelSpace (Rich d J E H t)]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
variable [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] [NeZero r]
variable (σ : Measure Seed) [IsProbabilityMeasure σ]
variable (t : ℕ) (policy : Machine.Policy Seed S (Point d J E H t) (Ordinary d J E H t) (Rich d J E H t))

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
    have hb := MarkVisibleQueries.original_repair_probability_bound (n := n) (ell := ell)
      P B fallback t leaf j policy σ hJ hP hB hPB hK0 N hell
    change ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P t).prod σ).real
      {w | MarkVisibleQueries.originalRepair (ell := ell) P B fallback t leaf j policy K N w}≤_ 
    apply hb.trans_eq
    simp only [familyBound,markBound,Nat.cast_mul]
    have he : -(1/8:ℝ)*(1/3072)^2*(r:ℝ)=-(r:ℝ)/75497472 := by ring
    rw [he]
    ring

def repairCount (K : ℝ) (N : ℕ) (w : Raw d n r J E H t × Seed) : ℕ :=
  ControllerRepairProbability.count
    (fun w : Raw d n r J E H t × Seed => rules (ell := ell) K (assemble P B fallback t w.1))
    (fun w => ControllerPolicyTrace.withOutput policy
      (JetLocality.ordinaryJet (scalar K t (assemble P B fallback t w.1)))
      (JetLocality.richJet (scalar K t (assemble P B fallback t w.1))) N w.2)
    (fun _ => TaskState.initial) w

theorem expected_repair_cost (Cp : ℝ)
    (hE : Module.finrank ℝ E=lowDimension Cp (4096*J^2+1))
    (hH : ∀ h,Module.finrank ℝ (H h)=levelDimension (lowDimension Cp (4096*J^2+1)) (cutoff (4096*J^2+1)) (h+2))
    (hJ : 4≤J) (hP : IsOrthogonalProjector P) (hB : Bᵀ*B=1) (hPB : P*B=B)
    {K : ℝ} (hK : 384≤K) (hCp : lowAllocation≤Cp)
    (hr : markAllocation*((4096*J^2+1:ℕ):ℝ)≤r) (N : ℕ) (hell : 0<ell) (hellM : ell≤4096*J^2+1) :
    (∫ w, (repairCount (ell := ell) P B fallback t policy K N w : ℝ)
      ∂((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P t).prod σ)) ≤
        (8:ℝ)^(t+1)*(4096*(J:ℝ)^2+1)/256 := by
  letI := RawHierarchy.law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P t
  have hK0 : 0<K := by linarith
  have ho : Measurable (fun q : Raw d n r J E H t × Point d J E H t =>
      JetLocality.ordinaryJet (scalar K t (assemble P B fallback t q.1)) q.2) :=
    (RawHierarchy.ordinaryJet_joint_measurable (n := n) (J := J) (E := E) (H := H) P B fallback hK0 t).mono
      le_rfl (le_of_eq BorelSpace.measurable_eq)
  have hv : Measurable (fun q : Raw d n r J E H t × Point d J E H t =>
      JetLocality.richJet (scalar K t (assemble P B fallback t q.1)) q.2) :=
    (RawHierarchy.richJet_joint_measurable (n := n) (J := J) (E := E) (H := H) P B fallback hK0 t).mono
      le_rfl (le_of_eq BorelSpace.measurable_eq)
  have hb := GeometricPolicyRepair.expected_repair_le_inventory_fraction (ell := ell)
    P B fallback t K (id : Raw d n r J E H t → _) measurable_id policy
    (fun raw => JetLocality.ordinaryJet (scalar K t (assemble P B fallback t raw)))
    (fun raw => JetLocality.richJet (scalar K t (assemble P B fallback t raw))) ho hv
    ((RawHierarchy.law P t).prod σ) N hell hellM Cp hK hCp hr
    (source_family_probability (n := n) (ell := ell) P B fallback σ t policy Cp hE hH hJ hP hB hPB (by linarith) N hell)
  exact hb

end GradientHessian.ActualRepairCost
