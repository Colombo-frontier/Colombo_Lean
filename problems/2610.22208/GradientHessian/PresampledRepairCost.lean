import GradientHessian.ActualRepairCost
import GradientHessian.PresampledConstruction

/-! The repair-cost theorem on the literal Euclidean presampled source.
Matrix validity, sphere laws and all allocated finranks are discharged by
the actual Settings, LowSpace and HighSpace definitions. -/

noncomputable section
namespace GradientHessian.PresampledConstruction
open MeasureTheory DirectionPolicyReplay RepairAllocation

variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (Cp : ℝ) (s : Settings)
variable [∀ t,MeasurableSpace (Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [∀ t,BorelSpace (Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [∀ t,MeasurableSpace (Ordinary s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [∀ t,BorelSpace (Ordinary s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [∀ t,MeasurableSpace (Rich s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [∀ t,BorelSpace (Rich s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
variable (σ : Measure Seed) [IsProbabilityMeasure σ]
variable (t : ℕ) (policy : Machine.Policy Seed S (Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)
  (Ordinary s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)
  (Rich s.D s.J (LowSpace Cp s) (HighSpace Cp s) t))

def repairCount {ell : ℕ} (K : ℝ) (N : ℕ) (w : Sample Cp s t × Seed) : ℕ :=
  ActualRepairCost.repairCount (ell := ell) s.P s.B 0 t policy K N w

theorem expected_repair_cost {ell : ℕ} {K : ℝ} (hK : 384≤K) (hCp : lowAllocation≤Cp)
    (hr : markAllocation*(s.M:ℝ)≤s.r) (N : ℕ) (hell : 0<ell) (hellM : ell≤s.M) :
    (∫ w, (repairCount (ell := ell) Cp s t policy K N w : ℝ) ∂(law Cp s t).prod σ) ≤
      (8:ℝ)^(t+1)*(s.M:ℝ)/256 := by
  have he : Module.finrank ℝ (LowSpace Cp s)=AllocationParameters.lowDimension Cp (4096*s.J^2+1) := by
    simp only [LowSpace,finrank_euclideanSpace_fin,Settings.M]
  have hh (h : ℕ) : Module.finrank ℝ (HighSpace Cp s h)=
      Allocation.levelDimension (AllocationParameters.lowDimension Cp (4096*s.J^2+1))
        (AllocationParameters.cutoff (4096*s.J^2+1)) (h+2) := by
    simp only [HighSpace,finrank_euclideanSpace_fin,Settings.M]
  have hb := ActualRepairCost.expected_repair_cost (n := s.columnsCount) (ell := ell)
    s.P s.B 0 σ t policy Cp he hh s.hJ (CanonicalSource.projector_orthogonal _)
    (CanonicalSource.columns_orthonormal _) (CanonicalSource.projector_columns _)
    hK hCp hr N hell hellM
  simpa only [repairCount,law,Settings.M,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using hb

end GradientHessian.PresampledConstruction
