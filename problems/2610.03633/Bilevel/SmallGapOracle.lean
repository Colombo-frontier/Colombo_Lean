import Bilevel.SmallGapSignal
import Bilevel.BernoulliOracle

/-! A genuine conservative Bernoulli oracle for the actual small-gap mean pair. -/

noncomputable section
namespace Bilevel.SmallGapInstance.Parameters

open scoped RealInnerProductSpace
open MeasureTheory SmallGapLiftSupport

variable (P : Parameters)

def publicY (x : ℝ) (y : LowerSpace) : LowerSpace :=
  (1 / 2 : ℝ) • (P.lowerY 1 x y + P.lowerY (-1) x y)

theorem publicLower_average (x : ℝ) (y : LowerSpace) :
    P.publicLower x y = (1 / 2 : ℝ) * (P.lower 1 x y + P.lower (-1) x y) := by
  have h1 := P.lower_sign_decomposition 1 x y (by norm_num)
  have h2 := P.lower_sign_decomposition (-1) x y (by norm_num)
  linarith

theorem publicLower_hasGradientY (x : ℝ) (y : LowerSpace) :
    HasGradientAt (P.publicLower x) (P.publicY x y) y := by
  have h := ((P.lower_hasGradientY 1 x y).hasFDerivAt.add
    (P.lower_hasGradientY (-1) x y).hasFDerivAt).const_mul (1 / 2 : ℝ)
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert h using 1
  · exact funext (P.publicLower_average x)
  ext v
  simp only [publicY, InnerProductSpace.toDual_apply, real_inner_smul_left, inner_add_left,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul]

theorem signedSignal_hasGradient (ω : ℝ) (y : LowerSpace) :
    HasGradientAt (fun v => ω * P.signal v) (ω • P.signalY y) y := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert (P.signal_hasGradientAt y).hasFDerivAt.const_mul ω using 1
  ext v
  simp only [InnerProductSpace.toDual_apply, real_inner_smul_left,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem publicLower_hasGradientX (x : ℝ) (y : LowerSpace) :
    HasGradientAt (fun v => P.publicLower v y) (P.lowerX 0 x y) x :=
  ((P.lower_hasGradientX 0 x y).hasDerivAt'.add_const
    (P.μ / (2 * P.L ^ 2) * (SmallGapProfileBounds.r1 P.S P.δ (y 0)) ^ 2)).hasGradientAt'

theorem lowerY_public_signal (ω x : ℝ) (y : LowerSpace) (hω : ω = 1 ∨ ω = -1) :
    P.lowerY ω x y = P.publicY x y + ω • P.signalY y := by
  rcases hω with hω | hω <;> subst ω <;> ext i <;> fin_cases i <;>
    simp [publicY, lowerY, lowerU, lowerS, signalY, signalU, signalS,
      P.residual_deriv, residual] <;> ring

def sampleLower (p ω x : ℝ) (y : LowerSpace) (b : Bool) : ℝ :=
  BernoulliOracle.sample p (P.publicLower x y) (ω * P.signal y) b

def sampleLowerY (p ω x : ℝ) (y : LowerSpace) (b : Bool) : LowerSpace :=
  BernoulliOracle.sample p (P.publicY x y) (ω • P.signalY y) b

def sampleLowerX (_p _ω x : ℝ) (y : LowerSpace) (_b : Bool) : ℝ := P.lowerX 0 x y

theorem sampleLower_hasGradientX (p ω x : ℝ) (y : LowerSpace) (b : Bool) :
    HasGradientAt (fun v => P.sampleLower p ω v y b) (P.sampleLowerX p ω x y b) x := by
  have h := (P.publicLower_hasGradientX x y).hasDerivAt'.add_const
    ((if b then p⁻¹ else 0) * (ω * P.signal y))
  simpa only [sampleLower, sampleLowerX, BernoulliOracle.sample, smul_eq_mul] using h.hasGradientAt'

theorem sampleLower_hasGradientY (p ω x : ℝ) (y : LowerSpace) (b : Bool) :
    HasGradientAt (fun v => P.sampleLower p ω x v b) (P.sampleLowerY p ω x y b) y :=
  BernoulliOracle.sample_hasGradient (P.publicLower_hasGradientY x y)
    (P.signedSignal_hasGradient ω y) p b

theorem sampleLowerY_mean (p ω x : ℝ) (y : LowerSpace) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hω : ω = 1 ∨ ω = -1) :
    (∫ b, P.sampleLowerY p ω x y b ∂BernoulliOracle.law p hp1) = P.lowerY ω x y := by
  rw [P.lowerY_public_signal ω x y hω]
  exact BernoulliOracle.sample_mean p hp0 hp1 (P.publicY x y) (ω • P.signalY y)

theorem signedSignal_bound (ω : ℝ) (y : LowerSpace) (hω : |ω| ≤ 1)
    (hscale : 4096 * C ^ 2 * P.S * P.R ≤ P.L) : ‖ω • P.signalY y‖ ≤ P.signalBound := by
  rw [norm_smul, Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_right hω (norm_nonneg (P.signalY y))
  have hw : |ω| * ‖P.signalY y‖ ≤ ‖P.signalY y‖ := by simpa only [one_mul] using h
  exact hw.trans (P.signal_gradient_bound_of_scale y hscale)

def activationProbability (σ : ℝ) : ℝ := BernoulliOracle.probability P.signalBound σ

theorem activationProbability_pos (σ : ℝ) : 0 < P.activationProbability σ :=
  BernoulliOracle.probability_pos P.signalBound_pos

theorem activationProbability_le_one (σ : ℝ) : P.activationProbability σ ≤ 1 :=
  BernoulliOracle.probability_le_one P.signalBound_pos

theorem sampleLowerY_variance (σ ω x : ℝ) (y : LowerSpace) (hω : ω = 1 ∨ ω = -1)
    (hscale : 4096 * C ^ 2 * P.S * P.R ≤ P.L) :
    (∫ b, ‖P.sampleLowerY (P.activationProbability σ) ω x y b - P.lowerY ω x y‖ ^ 2
      ∂BernoulliOracle.law (P.activationProbability σ) (P.activationProbability_le_one σ)) ≤ σ ^ 2 := by
  rw [P.lowerY_public_signal ω x y hω]
  have hω' : |ω| ≤ 1 := by rcases hω with h | h <;> simp [h]
  exact BernoulliOracle.bounded_variance P.signalBound_pos (P.publicY x y) (ω • P.signalY y)
    (P.signedSignal_bound ω y hω' hscale)

theorem sampleLower_full_variance (σ ω x : ℝ) (y : LowerSpace) (hω : ω = 1 ∨ ω = -1)
    (hscale : 4096 * C ^ 2 * P.S * P.R ≤ P.L) :
    (∫ b, (‖P.sampleLowerX (P.activationProbability σ) ω x y b - P.lowerX ω x y‖ ^ 2 +
      ‖P.sampleLowerY (P.activationProbability σ) ω x y b - P.lowerY ω x y‖ ^ 2)
      ∂BernoulliOracle.law (P.activationProbability σ) (P.activationProbability_le_one σ)) ≤ σ ^ 2 := by
  simpa only [sampleLowerX, lowerX, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] using
    P.sampleLowerY_variance σ ω x y hω hscale

theorem inactive_response_common (p x : ℝ) (y : LowerSpace) :
    P.sampleLowerY p 1 x y false = P.sampleLowerY p (-1) x y false := by
  simp [sampleLowerY, BernoulliOracle.sample]

theorem inverse_activationProbability (σ : ℝ) :
    (P.activationProbability σ)⁻¹ = 1 + σ ^ 2 / P.signalBound ^ 2 :=
  BernoulliOracle.inverse_probability P.signalBound_pos

theorem lower_joint_contDiff (ω : ℝ) :
    ContDiff ℝ 3 (fun v : ℝ × LowerSpace => P.lower ω v.1 v.2) := by
  have hx : ContDiff ℝ 3 (fun v : ℝ × LowerSpace => v.1) := contDiff_fst
  have h0 : ContDiff ℝ 3 (fun v : ℝ × LowerSpace => v.2 0) := p0.contDiff.comp contDiff_snd
  have h1 : ContDiff ℝ 3 (fun v : ℝ × LowerSpace => v.2 1) := p1.contDiff.comp contDiff_snd
  have h2 : ContDiff ℝ 3 (fun v : ℝ × LowerSpace => v.2 2) := p2.contDiff.comp contDiff_snd
  exact (((contDiff_const.mul ((h0.pow 2).add (h1.pow 2))).add
    (contDiff_const.mul (h2.pow 2))).sub ((contDiff_const.mul hx).mul h0) |>.sub
      (contDiff_const.mul (((SmallGapProfileBounds.r0_contDiff P.S P.R).comp h0).mul
        ((SmallGapProfiles.normal_contDiff P.R P.R_pos).comp h1) |>.sub
          ((contDiff_const.mul ((SmallGapProfileBounds.r1_contDiff P.S P.δ).comp h0)).mul
            ((SmallGapProfiles.normal_contDiff P.δ P.δ_pos).comp h1))))) |>.add
              (contDiff_const.mul (((P.residual_contDiff ω).comp h0).pow 2))

theorem publicLower_joint_contDiff :
    ContDiff ℝ 3 (fun v : ℝ × LowerSpace => P.publicLower v.1 v.2) := by
  have h0 : ContDiff ℝ 3 (fun v : ℝ × LowerSpace => v.2 0) := p0.contDiff.comp contDiff_snd
  exact (P.lower_joint_contDiff 0).add
    (contDiff_const.mul (((SmallGapProfileBounds.r1_contDiff P.S P.δ).comp h0).pow 2))

theorem signal_joint_contDiff : ContDiff ℝ 3 (fun v : ℝ × LowerSpace => P.signal v.2) := by
  have h0 : ContDiff ℝ 3 (fun v : ℝ × LowerSpace => v.2 0) := p0.contDiff.comp contDiff_snd
  have h1 : ContDiff ℝ 3 (fun v : ℝ × LowerSpace => v.2 1) := p1.contDiff.comp contDiff_snd
  have hr0 := (SmallGapProfileBounds.r0_contDiff P.S P.R).comp h0
  have hr1 := (SmallGapProfileBounds.r1_contDiff P.S P.δ).comp h0
  have hq := (SmallGapProfiles.normal_contDiff P.δ P.δ_pos).comp h1
  exact ((contDiff_const.mul hr1).mul hq).sub ((contDiff_const.mul hr0).mul hr1)

theorem sampleLower_joint_contDiff (p ω : ℝ) (b : Bool) :
    ContDiff ℝ 3 (fun v : ℝ × LowerSpace => P.sampleLower p ω v.1 v.2 b) := by
  exact P.publicLower_joint_contDiff.add
    (contDiff_const.mul (contDiff_const.mul P.signal_joint_contDiff))

end Bilevel.SmallGapInstance.Parameters
