import GradientHessian.NumericalEarlyExpectation
import GradientHessian.PresampledLowerParameters
import GradientHessian.PresampledRepairCost
import GradientHessian.GeometricPolicyProbability

/-! The finite-cutoff probability ledger for the literal presampled source.
All repair, validity and measurability premises are discharged. Its sole
remaining probabilistic input is the actual normal-early expectation. -/

noncomputable section
namespace GradientHessian.PresampledConstruction
open MeasureTheory DirectionPolicyReplay RepairAllocation HigherHierarchy JetLocality

variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (Cp : ℝ) (s : Settings)
variable [∀ t,MeasurableSpace (Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [∀ t,BorelSpace (Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [mO : ∀ t,MeasurableSpace (Ordinary s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [∀ t,BorelSpace (Ordinary s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [mV : ∀ t,MeasurableSpace (Rich s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [∀ t,BorelSpace (Rich s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
variable (σ : Measure Seed) [IsProbabilityMeasure σ]
variable (t : ℕ) (policy : Machine.Policy Seed S (Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)
  (Ordinary s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)
  (Rich s.D s.J (LowSpace Cp s) (HighSpace Cp s) t))

theorem source_column_split : s.columnsCount+s.κ*s.r=s.D := by
  have hj : 0<s.J := by have h := s.hJ; omega
  have hk : s.κ*s.r≤s.D := Nat.le_mul_of_pos_right _ hj
  exact Nat.sub_add_cancel hk

theorem expected_early_of_containment {K : ℝ} (hK : 0<K)
    (hJ : ForkLifetime.depthThreshold≤s.J) (hr : ForkLifetime.rankRatio*(s.M:ℝ)≤s.r) (N : ℕ)
    (hcontain : ∀ (leaf : FrontierState.Leaf (t+1)) (j : Fin (4096*s.J^2+1)),
      ∀ᵐ w ∂(law Cp s t).prod σ,
      w∈NumericalEarlyExpectation.earlyEvent (ell := ForkLifetime.lifetime s.J)
        s.P s.B 0 t leaf policy K N j →
      w∈NumericalForkProbability.rawEvent (ell := ForkLifetime.lifetime s.J)
        s.P s.B 0 t leaf policy hK j N) :
    (∫ w,(earlyCount (ell := ForkLifetime.lifetime s.J) Cp s t policy K N w:ℝ)
      ∂(law Cp s t).prod σ)≤(8:ℝ)^(t+1)*(s.M:ℝ)/256 := by
  have hell : 0<ForkLifetime.lifetime s.J := by
    have hh := ForkLifetime.lifetime_bounds hJ
    have hn : (1:ℝ)≤ForkLifetime.lifetime s.J := hh.2.1.trans hh.1
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hn)
  have hm := NumericalEarlyExpectation.early_mean_of_containment s.P s.B 0 t policy σ
    s.κ hJ hr s.hκ rfl (source_column_split s)
    (CanonicalSource.projector_orthogonal _) (CanonicalSource.projector_rank _)
    (CanonicalSource.columns_orthonormal _) (CanonicalSource.projector_columns _)
    rfl hell hK N hcontain
  simpa only [earlyCount,coefficients,objective,law,Settings.M,Nat.cast_add,Nat.cast_mul,
    Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using hm

end GradientHessian.PresampledConstruction
