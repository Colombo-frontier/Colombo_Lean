import GradientHessian.PresampledAugmentedEarlyAssembly
import GradientHessian.AugmentedLedgerProbability

noncomputable section
namespace GradientHessian.PresampledConstruction
open MeasureTheory AugmentedPolicy RepairAllocation HigherHierarchy JetLocality
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

theorem source_augmented_success_of_early {K : ℝ} (hK : 384≤K) (hCp : lowAllocation≤Cp)
    (hJ : ForkLifetime.depthThreshold≤s.J) (hrMark : markAllocation*(s.M:ℝ)≤s.r)
    (N G Hcap : ℕ)
    (hcaps : ∀ᵐ w ∂(law Cp s t).prod σ,AugmentedLedger.Caps (E := LowSpace Cp s) (H := HighSpace Cp s) s.P s.B 0 t policy K G Hcap w)
    (hrich : (Hcap:ℝ)≤(8:ℝ)^(t+1)/2)
    (hordinary : (G:ℝ)+1≤(8:ℝ)^(t+1)*(s.M:ℝ)*ForkLifetime.lifetime s.J/4)
    (hearly : (∫ w,(AugmentedEarlyPhase.earlyCount s.P s.B 0 t policy K N w:ℝ)
      ∂(law Cp s t).prod σ)≤(8:ℝ)^(t+1)*(s.M:ℝ)/256) :
    ((law Cp s t).prod σ).real {w | ‖gradient (objective Cp K s t w.1)
      (AugmentedLedger.output (E := LowSpace Cp s) (H := HighSpace Cp s) s.P s.B 0 t policy K N w)‖≤1}≤1/32 := by
  have hell : 0<ForkLifetime.lifetime s.J := by
    have hh := ForkLifetime.lifetime_bounds hJ
    have hn : (1:ℝ)≤ForkLifetime.lifetime s.J := hh.2.1.trans hh.1
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hn)
  have hvalid : ∀ᵐ w ∂(law Cp s t).prod σ,Valid _ _ _ _ t (coefficients Cp s t w.1) :=
    Measure.quasiMeasurePreserving_fst.ae (coefficients_valid Cp s t)
  have hrepair := expected_augmented_repair_cost Cp s σ t policy hK hCp hrMark N hell (lifetime_le_marked s.J)
  exact AugmentedLedger.success_probability (E := LowSpace Cp s) (H := HighSpace Cp s) s.P s.B 0 t policy ((law Cp s t).prod σ)
    (by linarith) N G Hcap hell hvalid hcaps hrich hordinary hearly hrepair

end GradientHessian.PresampledConstruction
