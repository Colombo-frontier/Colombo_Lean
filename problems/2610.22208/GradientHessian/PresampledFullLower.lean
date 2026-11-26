import GradientHessian.NumericalEarlyContainment
import GradientHessian.PresampledEarlyAssembly
import GradientHessian.PresampledParameterAssembly

/-! The literal chronological compiler for the original ordinary/rich-jet
policy class closes the remaining early-event premise. Consequently the presampled probability ledger, normalized
parameter theorem and minimax lower bound have no compiler or probability
estimate supplied as a hypothesis. -/

noncomputable section
namespace GradientHessian.PresampledConstruction
open MeasureTheory DirectionPolicyReplay RepairAllocation HigherHierarchy JetLocality

section Policy
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

theorem expected_early_cost {K : ℝ} (hK : 0<K)
    (hJ : ForkLifetime.depthThreshold≤s.J) (hr : ForkLifetime.rankRatio*(s.M:ℝ)≤s.r) (N : ℕ) :
    (∫ w,(earlyCount (ell := ForkLifetime.lifetime s.J) Cp s t policy K N w:ℝ)
      ∂(law Cp s t).prod σ)≤(8:ℝ)^(t+1)*(s.M:ℝ)/256 := by
  have hell : 0<ForkLifetime.lifetime s.J := by
    have hh := ForkLifetime.lifetime_bounds hJ
    have hn : (1:ℝ)≤ForkLifetime.lifetime s.J := hh.2.1.trans hh.1
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hn)
  apply expected_early_of_containment Cp s σ t policy hK hJ hr N
  intro leaf j
  have hvalid : ∀ᵐ w ∂(law Cp s t).prod σ,Valid _ _ _ _ t (coefficients Cp s t w.1) :=
    Measure.quasiMeasurePreserving_fst.ae (coefficients_valid Cp s t)
  filter_upwards [hvalid] with w hw
  intro he
  exact NumericalEarlyContainment.early_mem_rawEvent s.P s.B 0 t leaf policy hK hell w hw N j he

theorem source_success_probability_full {K : ℝ} (hK : 384≤K) (hCp : lowAllocation≤Cp)
    (hJ : ForkLifetime.depthThreshold≤s.J)
    (hrLife : ForkLifetime.rankRatio*(s.M:ℝ)≤s.r) (hrMark : markAllocation*(s.M:ℝ)≤s.r)
    (N G Hcap : ℕ)
    (hcaps : ∀ᵐ x ∂law Cp s t,policy.HasCaps (ordinaryJet (objective Cp K s t x))
      (richJet (objective Cp K s t x)) G Hcap)
    (hrich : (Hcap:ℝ)≤(8:ℝ)^(t+1)/2)
    (hordinary : (G:ℝ)+1≤(8:ℝ)^(t+1)*(s.M:ℝ)*ForkLifetime.lifetime s.J/4) :
    ((law Cp s t).prod σ).real {w | ‖gradient (objective Cp K s t w.1)
      (policy.output (policy.run (ordinaryJet (objective Cp K s t w.1))
        (richJet (objective Cp K s t w.1)) N w.2))‖≤1}≤1/32 := by
  have hell : 0<ForkLifetime.lifetime s.J := by
    have hh := ForkLifetime.lifetime_bounds hJ
    have hn : (1:ℝ)≤ForkLifetime.lifetime s.J := hh.2.1.trans hh.1
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hn)
  exact source_success_probability Cp s σ t policy hK hCp hrMark N G Hcap hell
    (lifetime_le_marked s.J) hcaps hrich hordinary
    (expected_early_cost Cp s σ t policy (by linarith) hJ hrLife N)

end Policy

attribute [local instance] physicalMeasurable physicalBorel allocatedMeasurable allocatedBorel
  firstMeasurable firstBorel secondMeasurable secondBorel allocatedFirstMeasurable allocatedFirstBorel
  allocatedSecondMeasurable allocatedSecondBorel ordinaryMeasurable ordinaryBorel richMeasurable richBorel

theorem normalized_early_bound (Cp : ℝ) {K : ℝ} (s : Settings) (t : ℕ) (hK : 0<K)
    (hJ : ForkLifetime.depthThreshold≤s.J) (hr : ForkLifetime.rankRatio*(s.M:ℝ)≤s.r) :
    NormalizedEarlyBound Cp K s t (ForkLifetime.lifetime s.J) := by
  intro A
  letI := A.seedSpace
  letI := A.stateSpace
  letI := A.probability
  intro N
  exact expected_early_cost Cp s A.seedLaw t
    (NormalizationPolicy.transport A.policy (normalizationScale K) (sourceCoordinates Cp s t)) hK hJ hr N

theorem source_uniform_parameter_lower : Model.UniformParameterLowerBound := by
  apply uniform_parameter_of_early
  intro J hJ t
  exact normalized_early_bound lowerCp (lowerSettings J hJ) t (by norm_num [lowerK])
    hJ (lowerSettings_rank J hJ).1

theorem source_main_lower : Model.MainLowerBound :=
  Model.uniformParameterLowerBound_implies_mainLowerBound source_uniform_parameter_lower

end GradientHessian.PresampledConstruction
