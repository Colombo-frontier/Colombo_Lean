import GradientHessian.AugmentedRepairCost
import GradientHessian.AugmentedOracleCorrectness
import GradientHessian.PresampledConstruction

/-! Full augmented comparison-policy repair cost on the literal Euclidean
presampled construction. No stopped-event, independence, measurability,
dimension, or oracle-agreement conclusion is assumed by the caller. -/

noncomputable section
namespace GradientHessian.PresampledConstruction
open MeasureTheory AugmentedPolicy RepairAllocation
open DirectionPolicyReplay (Point)

variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S] {ell : ℕ}
variable (Cp : ℝ) (s : Settings)
variable [∀ t,MeasurableSpace (Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [∀ t,BorelSpace (Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Ordinary s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [∀ t,BorelSpace (DirectionPolicyReplay.Ordinary s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Rich s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [∀ t,BorelSpace (DirectionPolicyReplay.Rich s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
variable (σ : Measure Seed) [IsProbabilityMeasure σ]
variable (t : ℕ) (policy : Machine.Policy (Seed × Packet s.D s.J (LowSpace Cp s) (HighSpace Cp s) t ell) S
  (Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)
  (Ordinary s.D s.J (LowSpace Cp s) (HighSpace Cp s) t ell)
  (Rich s.D s.J (LowSpace Cp s) (HighSpace Cp s) t ell))

def augmentedRepairCount (K : ℝ) (N : ℕ) (w : Sample Cp s t × Seed) : ℕ :=
  AugmentedPolicy.repairCount s.P s.B 0 t policy K N w

theorem expected_augmented_repair_cost {K : ℝ} (hK : 384≤K) (hCp : lowAllocation≤Cp)
    (hr : markAllocation*(s.M:ℝ)≤s.r) (N : ℕ) (hell : 0<ell) (hellM : ell≤s.M) :
    (∫ w, (augmentedRepairCount Cp s t policy K N w : ℝ) ∂(law Cp s t).prod σ) ≤
      (8:ℝ)^(t+1)*(s.M:ℝ)/256 := by
  have he : Module.finrank ℝ (LowSpace Cp s)=AllocationParameters.lowDimension Cp (4096*s.J^2+1) := by
    simp only [LowSpace,finrank_euclideanSpace_fin,Settings.M]
  have hh (h : ℕ) : Module.finrank ℝ (HighSpace Cp s h)=
      Allocation.levelDimension (AllocationParameters.lowDimension Cp (4096*s.J^2+1))
        (AllocationParameters.cutoff (4096*s.J^2+1)) (h+2) := by
    simp only [HighSpace,finrank_euclideanSpace_fin,Settings.M]
  have hb := AugmentedRepairCost.expected_repair_cost (n := s.columnsCount) (ell := ell)
    s.P s.B 0 σ t policy Cp he hh s.hJ (CanonicalSource.projector_orthogonal _)
    (CanonicalSource.columns_orthonormal _) (CanonicalSource.projector_columns _)
    hK hCp hr N hell hellM
  simpa only [augmentedRepairCount,law,Settings.M,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using hb

theorem augmented_replies_true_ae {K : ℝ} (hK : 0<K) (hell : 0<ell) :
    ∀ᵐ x ∂law Cp s t,
      ∀ (ps : List (ComparisonController.Pending (Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)))
        (p : ComparisonController.Pending (Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)),
      let d := coefficients Cp s t x
      let R := GeometricRepair.rules (ell := ell) K d
      let c := ComparisonController.serve R p (VisibilityWindow.run R ps TaskState.initial)
      AugmentedPolicy.ordinary s.P s.B 0 K t x c.beforeNormal c.afterNormal p.point=
          (JetLocality.ordinaryJet (objective Cp K s t x) p.point,AugmentedDisclosure.view K d c.afterNormal) ∧
        AugmentedPolicy.rich s.P s.B 0 K t x c.beforeNormal c.afterNormal p.point=
          (JetLocality.richJet (objective Cp K s t x) p.point,AugmentedDisclosure.view K d c.afterNormal) := by
  filter_upwards [coefficients_valid Cp s t] with x hx
  intro ps p
  exact AugmentedPolicy.prefix_true_replies s.P s.B 0 t x hK hx hell ps p

end GradientHessian.PresampledConstruction
