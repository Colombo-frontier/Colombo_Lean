import GradientHessian.PolicyRepairExpectation
import GradientHessian.GeometricRepairExpectation
import GradientHessian.RepairHeightAggregation

/-! The literal geometric controller on the original policy's adaptive
query trajectory, including its virtual output. Only the stopped-event
probability estimates remain inputs to the expected repair bound. -/

noncomputable section
namespace GradientHessian.GeometricPolicyRepair
open Classical Matrix LowRank HigherHierarchy TaskState TaskSlots ComparisonController
  ControllerMeasurable ControllerRepairProbability MeasureTheory Machine
  GeometricRepair PolicyRepairExpectation RepairHeightAggregation RepairAllocation

variable {Ω Seed S O V : Type*} [MeasurableSpace Ω] [MeasurableSpace Seed]
  [MeasurableSpace S] [MeasurableSpace O] [MeasurableSpace V]
variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h, NormedAddCommGroup (H h)] [∀ h, InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h, MeasurableSpace (H h)] [∀ h, BorelSpace (H h)] [∀ h, FiniteDimensional ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (K : ℝ)
  [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
variable (raw : Ω → RawHierarchy.Raw d n r J E H t) (hraw : Measurable raw)
  (Q : Policy Seed S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) O V)
  (o : Ω → Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t → O)
  (v : Ω → Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t → V)
  (ho : Measurable (fun q : Ω × Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t => o q.1 q.2))
  (hv : Measurable (fun q : Ω × Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t => v q.1 q.2))

def actualRules (q : Ω × Seed) := rules (ell := ell) K (RawHierarchy.assemble P B fallback t (raw q.1))

include hraw ho hv in
theorem expected_repair_le_families (μ : Measure (Ω × Seed)) [IsFiniteMeasure μ]
    (steps : ℕ) (hell : 0<ell) (loc : Fin t → ℝ) (old inner mark : ℝ)
    (hprob : ∀ a : Action t (4096*J^2),
      μ.real (event (actualRules (ell := ell) P B fallback t K raw)
        (policyPoints Q o v steps) (fun _ => initial) a) ≤ familyBound loc old inner mark a) :
    (∫ q, (count (actualRules (ell := ell) P B fallback t K raw)
      (policyPoints Q o v steps) (fun _ => initial) q : ℝ) ∂μ) ≤
      ∑ a : Action t (4096*J^2), (publicCost a:ℝ)*familyBound loc old inner mark a := by
  let tr := fun w => trigger (ell := ell) K (RawHierarchy.assemble P B fallback t (raw w))
  let hi := fun w => hit (ell := ell) (RawHierarchy.assemble P B fallback t (raw w))
  have htr := projected_trigger_measurable (ell := ell) P B fallback t K raw hraw
  have hhi := projected_hit_measurable (ell := ell) P B fallback t raw hraw
  have hb := mean_le_events (priority t (4096*J^2)) target tr hi htr hhi Q o v ho hv μ steps hell
  have hb' : (∫ q, (count (actualRules (ell := ell) P B fallback t K raw) (policyPoints Q o v steps)
    (fun _ => initial) q : ℝ) ∂μ) ≤
    ∑ a : Action t (4096*J^2), (publicCost a:ℝ)*μ.real
      (event (actualRules (ell := ell) P B fallback t K raw) (policyPoints Q o v steps) (fun _ => initial) a) := by
    simpa only [publicCost,Nat.cast_mul] using hb
  exact hb'.trans (Finset.sum_le_sum (fun a _ =>
    mul_le_mul_of_nonneg_left (hprob a) (Nat.cast_nonneg _)))

include hraw ho hv in
theorem expected_repair_le_inventory_fraction (μ : Measure (Ω × Seed)) [IsFiniteMeasure μ]
    (steps : ℕ) (hell : 0<ell) (hellM : ell≤4096*J^2+1)
    (Cp : ℝ) (hK : 384≤K) (hCp : lowAllocation≤Cp)
    (hr : markAllocation*((4096*J^2+1:ℕ):ℝ)≤r)
    (hprob : ∀ a : Action t (4096*J^2),
      μ.real (event (actualRules (ell := ell) P B fallback t K raw)
        (policyPoints Q o v steps) (fun _ => initial) a) ≤
        familyBound (fun h => localizedBound K Cp (4096*J^2+1) ell h.val)
          (oldBound Cp (4096*J^2+1) ell) (innerBound Cp (4096*J^2+1) ell)
          (markBound (4096*J^2+1) ell r) a) :
    (∫ q, (count (actualRules (ell := ell) P B fallback t K raw)
      (policyPoints Q o v steps) (fun _ => initial) q : ℝ) ∂μ) ≤
      (8:ℝ)^(t+1)*(4096*(J:ℝ)^2+1)/256 := by
  have hb := expected_repair_le_families P B fallback t K raw hraw Q o v ho hv μ steps hell
    _ _ _ _ hprob
  have hs := family_cost_bound hK hCp hellM hr t
  exact hb.trans (by simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hs)

end GradientHessian.GeometricPolicyRepair
