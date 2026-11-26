import FreshGradientMinimax.CoreThetaRoot
import FreshGradientMinimax.CoreThetaTail

/-! The original bounds |(sqrt Θ)'| ≤ 10 and |(sqrt Θ)''| ≤ 100,
obtained from the actual Gaussian tail and explicit derivatives. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem sqrt_tail_fraction_bounds {r d b : ℝ} (hr : 1 ≤ r) (hd : 0 < d) (hb : 0 < b)
    (hdb : d ≤ 9 * r * b ^ 2) (hgauss : r ^ 3 * d ≤ 8) :
    d / (2 * b) ≤ 10 ∧ r * d / (2 * b) ≤ 10 ∧ d ^ 2 / (4 * b ^ 3) ≤ 30 := by
  have hr0 : 0 < r := by linarith
  have hfirst : (r * d) ^ 2 ≤ 72 * b ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hdb (show 0 ≤ r ^ 2 * d by positivity)
    have h2 := mul_le_mul_of_nonneg_right hgauss (show 0 ≤ 9 * b ^ 2 by positivity)
    nlinarith only [h1, h2]
  have hrd : r * d ≤ 20 * b := (sq_le_sq₀ (by positivity) (by positivity)).mp (by
    nlinarith [sq_nonneg b])
  have hfour : d ^ 4 ≤ 5832 * b ^ 6 := by
    have hc := pow_le_pow_left₀ hd.le hdb 3
    have h1 := mul_le_mul_of_nonneg_right hc hd.le
    have h2 := mul_le_mul_of_nonneg_right hgauss (show 0 ≤ 729 * b ^ 6 by positivity)
    nlinarith only [h1, h2]
  have hs : d ^ 2 ≤ 120 * b ^ 3 := (sq_le_sq₀ (sq_nonneg d) (by positivity)).mp (by
    nlinarith [show 0 ≤ b ^ 6 by positivity])
  refine ⟨(div_le_iff₀ (by positivity)).mpr ?_, (div_le_iff₀ (by positivity)).mpr ?_,
    (div_le_iff₀ (by positivity)).mpr ?_⟩
  · have : d ≤ r * d := by nlinarith
    linarith
  · linarith
  · linarith

theorem coreThetaRoot_lower_above_neg_one {t : ℝ} (ht : -1 ≤ t) : 1 / 6 ≤ coreThetaRoot t := by
  have hs := coreThetaRoot_sq t
  have h := coreTheta_lower_above_neg_one ht
  nlinarith [coreThetaRoot_pos t]

theorem coreThetaRoot_tail_fractions {t : ℝ} (ht : t < -1) :
    coreThetaRootDeriv t ≤ 10 ∧ (-t) * coreDensity t / (2 * coreThetaRoot t) ≤ 10 ∧
      coreDensity t ^ 2 / (4 * coreThetaRoot t ^ 3) ≤ 30 := by
  have hr : 1 ≤ -t := by linarith
  have hl := coreTheta_tail_lower hr
  rw [neg_neg, coreDensity_neg] at hl
  have hdb : coreDensity t ≤ 9 * (-t) * coreThetaRoot t ^ 2 := by
    have h := (div_le_iff₀ (show 0 < 9 * (-t) by linarith)).mp hl
    rw [← coreThetaRoot_sq t] at h
    nlinarith only [h]
  have hg := coreDensity_cubic_tail hr
  rw [coreDensity_neg] at hg
  exact sqrt_tail_fraction_bounds hr (coreDensity_pos t) (coreThetaRoot_pos t) hdb hg

theorem coreThetaRoot_central_fractions {t : ℝ} (ht : -1 ≤ t) :
    coreThetaRootDeriv t ≤ 3 ∧ |t| * coreDensity t / (2 * coreThetaRoot t) ≤ 3 ∧
      coreDensity t ^ 2 / (4 * coreThetaRoot t ^ 3) ≤ 54 := by
  have hb := coreThetaRoot_lower_above_neg_one ht
  have hb0 := coreThetaRoot_pos t
  have hb3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 6) hb 3
  have hd := coreDensity_le_one t
  have hd2 : coreDensity t ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (coreDensity_pos t).le hd 2
    norm_num only [one_pow] at h
    exact h
  refine ⟨(div_le_iff₀ (by positivity)).mpr ?_, (div_le_iff₀ (by positivity)).mpr ?_,
    (div_le_iff₀ (by positivity)).mpr ?_⟩
  · linarith
  · linarith [coreDensity_abs_mul_le_one t]
  · norm_num at hb3
    nlinarith only [hb3, hd2]

theorem coreThetaRootDeriv_bound (t : ℝ) : |coreThetaRootDeriv t| ≤ 10 := by
  rw [abs_of_nonneg (coreThetaRootDeriv_nonneg t)]
  by_cases ht : -1 ≤ t
  · linarith [(coreThetaRoot_central_fractions ht).1]
  · exact (coreThetaRoot_tail_fractions (lt_of_not_ge ht)).1

theorem coreThetaRootSecond_bound (t : ℝ) : |coreThetaRootSecond t| ≤ 100 := by
  have hb := coreThetaRoot_pos t
  have hd := coreDensity_pos t
  have hden : 0 < 2 * coreThetaRoot t := mul_pos (by norm_num) hb
  have he : |-t * coreDensity t / (2 * coreThetaRoot t)| =
      |t| * coreDensity t / (2 * coreThetaRoot t) := by
    rw [abs_div, abs_mul, abs_neg, abs_of_pos hd, abs_of_pos hden]
  have hs : |coreDensity t ^ 2 / (4 * coreThetaRoot t ^ 3)| =
      coreDensity t ^ 2 / (4 * coreThetaRoot t ^ 3) := abs_of_nonneg (by positivity)
  have h := abs_sub (-t * coreDensity t / (2 * coreThetaRoot t))
    (coreDensity t ^ 2 / (4 * coreThetaRoot t ^ 3))
  rw [he, hs] at h
  change |coreThetaRootSecond t| ≤ _ at h
  by_cases ht : -1 ≤ t
  · have hh := coreThetaRoot_central_fractions ht
    linarith [hh.2.1, hh.2.2]
  · have hneg : t < 0 := by linarith
    rw [abs_of_neg hneg] at h
    have hh := coreThetaRoot_tail_fractions (lt_of_not_ge ht)
    linarith [hh.2.1, hh.2.2]

end FreshGradientMinimax
