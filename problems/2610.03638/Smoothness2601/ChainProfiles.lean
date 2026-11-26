import Smoothness2601.Cutoffs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The actual integral profile used by the extensive chain. Since zeta
vanishes outside [-2,2], the finite lower endpoint -2 represents the source's
integral from negative infinity without an improper-integral convention. -/
noncomputable section
namespace Smoothness2601.ChainProfiles
open Cutoffs MeasureTheory Set Filter
open scoped Topology ContDiff

def profile (M t : ℝ) : ℝ := M * ∫ u in (-2 : ℝ)..t, zeta u

theorem zeta_continuous : Continuous zeta := (zeta_contDiff 0).continuous

theorem zeta_intervalIntegrable (a b : ℝ) : IntervalIntegrable zeta volume a b :=
  zeta_continuous.intervalIntegrable a b

theorem profile_hasDerivAt (M t : ℝ) : HasDerivAt (profile M) (M * zeta t) t := by
  exact (intervalIntegral.integral_hasDerivAt_right (zeta_intervalIntegrable (-2) t)
    zeta_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter zeta_continuous.continuousAt).const_mul M

theorem profile_deriv (M t : ℝ) : deriv (profile M) t = M * zeta t := (profile_hasDerivAt M t).deriv

theorem profile_smooth (M : ℝ) : ContDiff ℝ ∞ (profile M) := by
  apply contDiff_infty_iff_deriv.mpr
  constructor
  · exact fun t => (profile_hasDerivAt M t).differentiableAt
  · have he : deriv (profile M) = fun t => M * zeta t := funext (profile_deriv M)
    rw [he]
    exact contDiff_const.mul (zeta_contDiff ⊤)

theorem profile_deriv_nonneg {M : ℝ} (hM : 0 ≤ M) (t : ℝ) : 0 ≤ deriv (profile M) t := by
  rw [profile_deriv]
  exact mul_nonneg hM (zeta_nonneg t)

theorem profile_monotone {M : ℝ} (hM : 0 ≤ M) : Monotone (profile M) :=
  monotone_of_deriv_nonneg (fun t => (profile_hasDerivAt M t).differentiableAt)
    (profile_deriv_nonneg hM)

theorem profile_zero_left (M : ℝ) {t : ℝ} (ht : t ≤ -2) : profile M t = 0 := by
  have hz : (∫ u in (-2 : ℝ)..t, zeta u) = 0 := by
    calc
      _ = ∫ u in (-2 : ℝ)..t, (0 : ℝ) := intervalIntegral.integral_congr (by
        intro u hu
        have hu' : u ≤ -2 := hu.2.trans (max_le le_rfl ht)
        exact zeta_zero_far (by rw [abs_of_nonpos (by linarith : u ≤ 0)]; linarith))
      _ = 0 := by simp
  simp [profile, hz]

theorem profile_constant_right (M : ℝ) {t : ℝ} (ht : 2 ≤ t) : profile M t = profile M 2 := by
  have hz : (∫ u in (2 : ℝ)..t, zeta u) = 0 := by
    calc
      _ = ∫ u in (2 : ℝ)..t, (0 : ℝ) := intervalIntegral.integral_congr (by
        intro u hu
        have hu' : 2 ≤ u := (le_min le_rfl ht).trans hu.1
        exact zeta_zero_far (by rw [abs_of_nonneg (by linarith : 0 ≤ u)]; exact hu'))
      _ = 0 := by simp
  have h := intervalIntegral.integral_add_adjacent_intervals (zeta_intervalIntegrable (-2) 2)
    (zeta_intervalIntegrable 2 t)
  rw [hz, add_zero] at h
  simp only [profile, ← h]

theorem profile_nonneg {M : ℝ} (hM : 0 ≤ M) (t : ℝ) : 0 ≤ profile M t := by
  by_cases ht : t ≤ -2
  · rw [profile_zero_left M ht]
  · have h := profile_monotone hM (le_of_not_ge ht)
    rwa [profile_zero_left M (le_refl (-2))] at h

theorem profile_le_four_mul {M : ℝ} (hM : 0 ≤ M) (t : ℝ) : profile M t ≤ 4 * M := by
  have h2 : profile M 2 ≤ 4 * M := by
    have hi := intervalIntegral.integral_mono (by norm_num : (-2 : ℝ) ≤ 2)
      (zeta_intervalIntegrable (-2) 2) (continuous_const.intervalIntegrable (-2 : ℝ) 2)
      zeta_le_one
    have hi' : (∫ u in (-2 : ℝ)..2, zeta u) ≤ 4 := by norm_num at hi; exact hi
    unfold profile
    nlinarith [mul_le_mul_of_nonneg_left hi' hM]
  rcases le_total t 2 with ht | ht
  · exact (profile_monotone hM ht).trans h2
  · rwa [profile_constant_right M ht]

theorem profile_deriv_even (M t : ℝ) : deriv (profile M) (-t) = deriv (profile M) t := by
  simp only [profile_deriv, zeta_even]

theorem profile_deriv_zero_near (M : ℝ) {t : ℝ} (ht : |t| ≤ 1/16) :
    deriv (profile M) t = 0 := by rw [profile_deriv, zeta_zero_near ht, mul_zero]

theorem profile_deriv_plateau (M : ℝ) {t : ℝ} (hl : 1/8 ≤ |t|) (hu : |t| ≤ 1) :
    deriv (profile M) t = M := by rw [profile_deriv, zeta_one hl hu, mul_one]

theorem profile_constant_near (M : ℝ) {u v : ℝ} (hu : |u| ≤ 1/16) (hv : |v| ≤ 1/16) :
    profile M u = profile M v := by
  obtain ⟨hu0, hu1⟩ := abs_le.mp hu
  obtain ⟨hv0, hv1⟩ := abs_le.mp hv
  have hz : (∫ t in u..v, zeta t) = 0 := by
    calc
      _ = ∫ t in u..v, (0 : ℝ) := intervalIntegral.integral_congr (by
        intro t ht
        apply zeta_zero_near
        apply abs_le.mpr
        exact ⟨(le_min hu0 hv0).trans ht.1, ht.2.trans (max_le hu1 hv1)⟩)
      _ = 0 := by simp
  have h := intervalIntegral.integral_add_adjacent_intervals (zeta_intervalIntegrable (-2) u)
    (zeta_intervalIntegrable u v)
  rw [hz, add_zero] at h
  simp only [profile, h]

theorem psi_deriv_zero {t : ℝ} (ht : t < 1/2) : deriv psi t = 0 := by
  have he : psi =ᶠ[𝓝 t] (fun _ => 0) := by
    filter_upwards [gt_mem_nhds ht] with u hu
    exact psi_zero hu.le
  simpa using he.deriv_eq

theorem bump_deriv_identity {t : ℝ} (ht : |t| < 1/8) : deriv bump t = 1 := by
  have he : bump =ᶠ[𝓝 t] id := by
    filter_upwards [continuous_abs.continuousAt.eventually (gt_mem_nhds ht)] with u hu
    exact bump_identity hu.le
  simpa using he.deriv_eq

end Smoothness2601.ChainProfiles
