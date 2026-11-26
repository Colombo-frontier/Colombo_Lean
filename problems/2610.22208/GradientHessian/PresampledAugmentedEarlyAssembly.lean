import GradientHessian.AugmentedEarlyProbability
import GradientHessian.PresampledEarlyAssembly
import GradientHessian.PresampledAugmentedRepairCost

noncomputable section
namespace GradientHessian.PresampledConstruction
open MeasureTheory AugmentedPolicy RepairAllocation HigherHierarchy
open DirectionPolicyReplay (Point)

variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S] 
variable (Cp : ℝ) (s : Settings)
variable [∀ t,MeasurableSpace (Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [∀ t,BorelSpace (Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Ordinary s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [∀ t,BorelSpace (DirectionPolicyReplay.Ordinary s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Rich s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [∀ t,BorelSpace (DirectionPolicyReplay.Rich s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
variable (σ : Measure Seed) [IsProbabilityMeasure σ]
variable (t : ℕ) (policy : Machine.Policy (Seed × Packet s.D s.J (LowSpace Cp s) (HighSpace Cp s) t (ForkLifetime.lifetime s.J)) S
  (Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)
  (Ordinary s.D s.J (LowSpace Cp s) (HighSpace Cp s) t (ForkLifetime.lifetime s.J))
  (Rich s.D s.J (LowSpace Cp s) (HighSpace Cp s) t (ForkLifetime.lifetime s.J)))

theorem expected_augmented_early_of_containment {K : ℝ} (hK : 0<K)
    (hJ : ForkLifetime.depthThreshold≤s.J) (hr : ForkLifetime.rankRatio*(s.M:ℝ)≤s.r) (N : ℕ)
    (hcontain : ∀ (leaf : FrontierState.Leaf (t+1)) (j : Fin (4096*s.J^2+1)),
      ∀ᵐ w ∂(law Cp s t).prod σ,
      w∈AugmentedEarlyPhase.earlyEvent s.P s.B 0 t policy K N leaf j →
      w∈AugmentedNumericalProbability.rawEvent (ell := ForkLifetime.lifetime s.J)
        s.P s.B 0 t leaf policy hK j N) :
    (∫ w,(AugmentedEarlyPhase.earlyCount s.P s.B 0 t policy K N w:ℝ)
      ∂(law Cp s t).prod σ)≤(8:ℝ)^(t+1)*(s.M:ℝ)/256 := by
  have hell : 0<ForkLifetime.lifetime s.J := by
    have hh := ForkLifetime.lifetime_bounds hJ
    have hn : (1:ℝ)≤ForkLifetime.lifetime s.J := hh.2.1.trans hh.1
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hn)
  have hm := AugmentedEarlyPhase.early_mean_of_containment s.P s.B 0 t policy σ
    s.κ hJ hr s.hκ rfl (source_column_split s)
    (CanonicalSource.projector_orthogonal _) (CanonicalSource.projector_rank _)
    (CanonicalSource.columns_orthonormal _) (CanonicalSource.projector_columns _)
    rfl hell hK N hcontain
  simpa only [law,Settings.M,Nat.cast_add,Nat.cast_mul,
    Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using hm


end GradientHessian.PresampledConstruction
