import GradientHessian.PresampledNormalizedProbability
import GradientHessian.ForkLifetime
import GradientHessian.PaddingReduction

/-! Explicit absolute choices and the quantitative lifetime-to-minimax
conversion. The remaining early expectation is kept as its literal integral,
not replaced by a model lower-bound assumption. -/

noncomputable section
namespace GradientHessian.PresampledConstruction
open MeasureTheory HigherHierarchy RepairAllocation

attribute [local instance] physicalMeasurable physicalBorel allocatedMeasurable allocatedBorel
  firstMeasurable firstBorel secondMeasurable secondBorel allocatedFirstMeasurable allocatedFirstBorel
  allocatedSecondMeasurable allocatedSecondBorel ordinaryMeasurable ordinaryBorel richMeasurable richBorel

def lowerRankConstant : ℝ := max ForkLifetime.rankRatio markAllocation
def lowerCp : ℝ := lowAllocation
def lowerK : ℝ := 384
def lowerKappa : ℕ := 18874368
def lowerRateConstant : ℝ := ForkLifetime.lifetimeFraction/1040

theorem lowerRankConstant_ge_one : 1≤lowerRankConstant :=
  (le_trans (by norm_num) ForkLifetime.rankRatio_ge).trans (le_max_left _ _)

theorem lower_J_ge_four {J : ℕ} (hJ : ForkLifetime.depthThreshold≤J) : 4≤J := by
  have hd := ForkLifetime.depth_lower hJ
  have hs := ForkLifetime.overlapScale_ge_one
  exact_mod_cast (show (4:ℝ)≤J by linarith)

def lowerSettings (J : ℕ) (hJ : ForkLifetime.depthThreshold≤J) : Settings :=
  Settings.ofScale J lowerKappa lowerRankConstant (lower_J_ge_four hJ) le_rfl lowerRankConstant_ge_one

theorem lowerSettings_rank (J : ℕ) (hJ : ForkLifetime.depthThreshold≤J) :
    ForkLifetime.rankRatio*((lowerSettings J hJ).M:ℝ)≤(lowerSettings J hJ).r ∧
      markAllocation*((lowerSettings J hJ).M:ℝ)≤(lowerSettings J hJ).r := by
  have hc := Nat.le_ceil (lowerRankConstant*(1+4096*(J:ℝ)^2))
  have hm : (0:ℝ)≤1+4096*(J:ℝ)^2 := by positivity
  have hh : ((lowerSettings J hJ).M:ℝ)=1+4096*(J:ℝ)^2 := by
    simp [lowerSettings,Settings.ofScale,Settings.M]; ring
  rw [hh]
  constructor
  · exact (mul_le_mul_of_nonneg_right (le_max_left _ _) hm).trans hc
  · exact (mul_le_mul_of_nonneg_right (le_max_right _ _) hm).trans hc

theorem lifetime_le_marked (J : ℕ) : ForkLifetime.lifetime J≤4096*J^2+1 := by
  have hf := Nat.floor_le (mul_nonneg ForkLifetime.lifetimeFraction_pos.le (Nat.cast_nonneg J))
  change (ForkLifetime.lifetime J:ℝ)≤ForkLifetime.lifetimeFraction*(J:ℝ) at hf
  have hc := mul_le_mul_of_nonneg_right ForkLifetime.lifetimeFraction_le (Nat.cast_nonneg J)
  have hsq : (J:ℝ)≤(J:ℝ)^2+1 := by nlinarith [sq_nonneg ((J:ℝ)-1)]
  exact_mod_cast (show (ForkLifetime.lifetime J:ℝ)≤4096*(J:ℝ)^2+1 by nlinarith [sq_nonneg (J:ℝ)])

theorem source_sqrt_le {J : ℕ} (hJ : 1≤J) : Real.sqrt (1+4096*(J:ℝ)^2)≤65*J := by
  have hj : (1:ℝ)≤J := by exact_mod_cast hJ
  have hs := Real.sq_sqrt (by positivity : (0:ℝ)≤1+4096*(J:ℝ)^2)
  have hn := Real.sqrt_nonneg (1+4096*(J:ℝ)^2)
  nlinarith [sq_nonneg ((J:ℝ)-1)]

theorem lower_rate_le_slots {J : ℕ} (hJ : ForkLifetime.depthThreshold≤J) {n : ℝ} (hn : 0≤n) :
    lowerRateConstant*n*(1+4096*(J:ℝ)^2)^(3/2:ℝ)≤
      n*(1+4096*(J:ℝ)^2)*ForkLifetime.lifetime J/8 := by
  have hf := (ForkLifetime.lifetime_bounds hJ).1
  have hs := source_sqrt_le (show 1≤J from (by have := lower_J_ge_four hJ; omega))
  have hc := mul_le_mul_of_nonneg_left hs ForkLifetime.lifetimeFraction_pos.le
  have hp : lowerRateConstant*Real.sqrt (1+4096*(J:ℝ)^2)≤(ForkLifetime.lifetime J:ℝ)/8 := by
    unfold lowerRateConstant
    nlinarith
  have hm : 0≤n*(1+4096*(J:ℝ)^2) := by positivity
  have hb := mul_le_mul_of_nonneg_left hp hm
  rw [← PhysicalDimension.mul_sqrt_eq_rpow (by positivity : (0:ℝ)<1+4096*(J:ℝ)^2)]
  nlinarith

def NormalizedEarlyBound (Cp K : ℝ) (s : Settings) (t ell : ℕ) : Prop :=
  ∀ A : Model.Algorithm (PhysicalDimension.count Cp s.D s.M (t+1)),
    letI := A.seedSpace
    letI := A.stateSpace
    ∀ N : ℕ,(∫ w,(earlyCount (ell := ell) Cp s t
      (NormalizationPolicy.transport A.policy (normalizationScale K) (sourceCoordinates Cp s t)) K N w:ℝ)
      ∂(law Cp s t).prod A.seedLaw)≤(8:ℝ)^(t+1)*(s.M:ℝ)/256

theorem complexity_of_early {Cp K T : ℝ} (s : Settings) (t ell Hcap : ℕ)
    (hK : 384≤K) (hCp : lowAllocation≤Cp) (hr : markAllocation*(s.M:ℝ)≤s.r)
    (hell : 0<ell) (hellM : ell≤s.M) (hrich : (Hcap:ℝ)≤(8:ℝ)^(t+1)/2)
    (hT : normalizedGapConstant K*8^(t+1)*s.M≤T)
    (hearly : NormalizedEarlyBound Cp K s t ell) :
    ENNReal.ofReal ((8:ℝ)^(t+1)*(s.M:ℝ)*ell/8)≤
      Model.complexity Hcap (PhysicalDimension.count Cp s.D s.M (t+1)) T := by
  apply Model.complexity_lower_of_failure
  intro G hG A
  have hn : (8:ℝ)≤(8:ℝ)^(t+1) := by
    have hh : (1:ℝ)≤8^t := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    linarith
  have hm : (1:ℝ)≤s.M := by
    simp only [Settings.M,Nat.cast_add,Nat.cast_one]
    linarith [Nat.cast_nonneg (α := ℝ) (4096*s.J^2)]
  have hl : (1:ℝ)≤ell := by exact_mod_cast hell
  have hprod : (8:ℝ)≤(8:ℝ)^(t+1)*(s.M:ℝ)*ell :=
    le_trans (by norm_num) (mul_le_mul (mul_le_mul hn hm (by norm_num) (by positivity)) hl (by norm_num) (by positivity))
  apply normalized_no_guarantee Cp s t hK hCp hr G Hcap hell hellM hrich (by linarith) hT A
  exact hearly A

end GradientHessian.PresampledConstruction
