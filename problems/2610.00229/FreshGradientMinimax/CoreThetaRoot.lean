import FreshGradientMinimax.CoreGateSmooth
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Smoothness, reflection, and exact derivatives of the positive Gaussian
primitive and its square root. Uniform derivative bounds are proved separately. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open Real MeasureTheory Set

theorem coreDensity_neg (t : ℝ) : coreDensity (-t) = coreDensity t := by
  simp only [coreDensity, neg_sq]

theorem coreTheta_reflection (t : ℝ) : coreTheta (-t) = coreThetaMass - coreTheta t := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
    (Homeomorph.neg ℝ).measurableEmbedding ((Iic (-t)).indicator coreDensity)
  have hg : (fun x => (Iic (-t)).indicator coreDensity (-x)) = (Ici t).indicator coreDensity := by
    funext x
    simp only [indicator, mem_Iic, mem_Ici, neg_le_neg_iff, coreDensity_neg]
  rw [hg, integral_indicator measurableSet_Ici, integral_indicator measurableSet_Iic,
    integral_Ici_eq_integral_Ioi] at h
  have hs := intervalIntegral.integral_Iic_add_Ioi (b := t)
    coreDensity_integrable.integrableOn coreDensity_integrable.integrableOn
  rw [h, coreDensity_integral] at hs
  change coreTheta t + coreTheta (-t) = coreThetaMass at hs
  linarith

theorem coreDensity_hasDerivAt (t : ℝ) : HasDerivAt coreDensity (-t * coreDensity t) t := by
  convert ((((hasDerivAt_id t).pow 2).neg).div_const 2).exp using 1
  simp only [coreDensity, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

theorem coreTheta_contDiff {n : ℕ∞} : ContDiff ℝ n coreTheta := by
  apply contDiff_all_iff_nat.2 (fun m => ?_) n
  cases m with
  | zero => exact contDiff_zero.mpr coreTheta_continuous
  | succ m =>
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = m + 1 from rfl]
    refine contDiff_succ_iff_deriv.mpr ⟨fun t => (coreTheta_hasDerivAt t).differentiableAt, by simp, ?_⟩
    rw [show deriv coreTheta = coreDensity from funext coreTheta_deriv]
    unfold coreDensity
    have hc : ContDiff ℝ (m : ℕ) (fun t : ℝ => -(1 / 2 : ℝ) * t ^ 2) :=
      contDiff_const.mul (contDiff_id.pow 2)
    convert hc.exp using 1
    funext t
    congr 1
    ring

def coreThetaRoot (t : ℝ) : ℝ := sqrt (coreTheta t)
def coreThetaRootDeriv (t : ℝ) : ℝ := coreDensity t / (2 * coreThetaRoot t)
def coreThetaRootSecond (t : ℝ) : ℝ :=
  -t * coreDensity t / (2 * coreThetaRoot t) - coreDensity t ^ 2 / (4 * coreThetaRoot t ^ 3)

theorem coreThetaRoot_pos (t : ℝ) : 0 < coreThetaRoot t := sqrt_pos.mpr (coreTheta_pos t)

theorem coreThetaRoot_sq (t : ℝ) : coreThetaRoot t ^ 2 = coreTheta t := sq_sqrt (coreTheta_pos t).le

theorem coreThetaRoot_bound (t : ℝ) : |coreThetaRoot t| ≤ 2 := by
  rw [abs_of_pos (coreThetaRoot_pos t)]
  nlinarith [coreThetaRoot_sq t, coreTheta_lt_three t]

theorem coreThetaRoot_contDiff {n : ℕ∞} : ContDiff ℝ n coreThetaRoot :=
  coreTheta_contDiff.sqrt (fun t => (coreTheta_pos t).ne')

theorem coreThetaRoot_hasDerivAt (t : ℝ) : HasDerivAt coreThetaRoot (coreThetaRootDeriv t) t :=
  (coreTheta_hasDerivAt t).sqrt (coreTheta_pos t).ne'

theorem coreThetaRootDeriv_hasDerivAt (t : ℝ) :
    HasDerivAt coreThetaRootDeriv (coreThetaRootSecond t) t := by
  have hb : coreThetaRoot t ≠ 0 := (coreThetaRoot_pos t).ne'
  have hd := (coreDensity_hasDerivAt t).div ((coreThetaRoot_hasDerivAt t).const_mul 2)
    (mul_ne_zero (by norm_num) hb)
  convert hd using 1
  unfold coreThetaRootSecond coreThetaRootDeriv
  field_simp
  ring

theorem coreThetaRoot_deriv (t : ℝ) : deriv coreThetaRoot t = coreThetaRootDeriv t :=
  (coreThetaRoot_hasDerivAt t).deriv

theorem coreThetaRoot_second (t : ℝ) : deriv (deriv coreThetaRoot) t = coreThetaRootSecond t := by
  rw [show deriv coreThetaRoot = coreThetaRootDeriv from funext coreThetaRoot_deriv]
  exact (coreThetaRootDeriv_hasDerivAt t).deriv

theorem coreThetaRootDeriv_nonneg (t : ℝ) : 0 ≤ coreThetaRootDeriv t :=
  div_nonneg (coreDensity_pos t).le (mul_nonneg (by norm_num) (coreThetaRoot_pos t).le)

end FreshGradientMinimax
