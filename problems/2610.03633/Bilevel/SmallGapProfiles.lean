import Bilevel.SepticRegularity
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # The actual profiles of the small-gap construction -/

noncomputable section
namespace Bilevel.SmallGapProfiles
open scoped Topology
open Filter MeasureTheory

def integrand (v : ℝ) : ℝ := v * (1 - SmallGap.septicStep (v - 1))
def phi (t : ℝ) : ℝ := ∫ v in (0 : ℝ)..|t|, integrand v
def psi (t : ℝ) : ℝ := t * (1 - SmallGap.septicStep ((|t| - 2) / 32))
/- The fixed normal is genuinely C-infinity. Its value and plateau interfaces
are unchanged; constants below are derived from the actual new profile. -/
def normal (a s : ℝ) : ℝ := s * (1 - Real.smoothTransition ((16*(s/a)^2-1)/3))

theorem step_zero {t : ℝ} (h : t ≤ 0) : SmallGap.septicStep t = 0 := by
  simp only [SmallGap.septicStep, if_pos h]

theorem step_one {t : ℝ} (h : 1 ≤ t) : SmallGap.septicStep t = 1 := by
  have hn : ¬ t ≤ 0 := by linarith
  simp only [SmallGap.septicStep, if_neg hn, if_pos h]

theorem integrand_continuous : Continuous integrand := by
  unfold integrand
  exact continuous_id.mul (continuous_const.sub
    (SepticRegularity.septicStep_contDiff.continuous.comp (continuous_id.sub continuous_const)))

theorem integrand_core (v : ℝ) (hv : v ≤ 1) : integrand v = v := by
  simp [integrand, step_zero (by linarith : v - 1 ≤ 0)]

theorem integrand_zero (v : ℝ) (hv : 2 ≤ v) : integrand v = 0 := by
  simp [integrand, step_one (by linarith : 1 ≤ v - 1)]

theorem phi_even (t : ℝ) : phi (-t) = phi t := by simp [phi]

theorem phi_core (t : ℝ) (ht : |t| ≤ 1) : phi t = t ^ 2 / 2 := by
  have he : (∫ v in (0 : ℝ)..|t|, integrand v) = ∫ v in (0 : ℝ)..|t|, v := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (abs_nonneg t)] at hv
    exact integrand_core v (hv.2.trans ht)
  rw [phi, he, integral_id]
  simp [sq_abs]

theorem phi_nonneg (t : ℝ) : 0 ≤ phi t := by
  apply intervalIntegral.integral_nonneg (abs_nonneg t)
  intro v hv
  exact mul_nonneg hv.1 (sub_nonneg.mpr (SmallGap.septicStep_range (v - 1)).2)

theorem phi_le_quadratic (t : ℝ) : phi t ≤ t ^ 2 / 2 := by
  have h := intervalIntegral.integral_mono_on (μ := volume) (abs_nonneg t)
    (integrand_continuous.intervalIntegrable 0 |t|)
    (continuous_id.intervalIntegrable 0 |t|) (fun v hv => ?_)
  · simpa [phi, integral_id, sq_abs] using h
  · have hs := (SmallGap.septicStep_range (v - 1)).1
    dsimp [integrand]
    nlinarith [hv.1]

theorem phi_constant_tail (t : ℝ) (ht : 2 ≤ |t|) : phi t = phi 2 := by
  have hzero : (∫ v in (2 : ℝ)..|t|, integrand v) = 0 := by
    calc
      _ = ∫ _v in (2 : ℝ)..|t|, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [Set.uIcc_of_le ht] at hv
        exact integrand_zero v hv.1
      _ = 0 := by simp
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (integrand_continuous.intervalIntegrable 0 2)
    (integrand_continuous.intervalIntegrable 2 |t|)
  simpa [phi, hzero] using h.symm

theorem phi_hasDerivAt (t : ℝ) :
    HasDerivAt phi (t * (1 - SmallGap.septicStep (|t| - 1))) t := by
  have hi := intervalIntegral.integral_hasDerivAt_right
    (integrand_continuous.intervalIntegrable 0 |t|)
    (integrand_continuous.stronglyMeasurableAtFilter volume _) integrand_continuous.continuousAt
  rcases lt_trichotomy t 0 with ht | ht | ht
  · convert hi.comp t (hasDerivAt_abs_neg ht) using 1
    dsimp [integrand]
    rw [abs_of_neg ht]
    ring
  · subst t
    have hq : HasDerivAt (fun t : ℝ => t ^ 2 / 2) 0 0 := by
      convert ((hasDerivAt_id (0 : ℝ)).pow 2).div_const 2 using 1
      norm_num
    simpa only [zero_mul] using hq.congr_of_eventuallyEq (show phi =ᶠ[𝓝 0]
        (fun t : ℝ => t ^ 2 / 2) from by
      filter_upwards [eventually_gt_nhds (by norm_num : (-1 : ℝ) < 0),
        eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)] with v hv0 hv1
      exact phi_core v (abs_le.mpr ⟨hv0.le, hv1.le⟩))
  · convert hi.comp t (hasDerivAt_abs_pos ht) using 1
    dsimp [integrand]
    rw [abs_of_pos ht]
    ring

theorem phi_deriv (t : ℝ) : deriv phi t = t * (1 - SmallGap.septicStep (|t| - 1)) :=
  (phi_hasDerivAt t).deriv

theorem psi_odd (t : ℝ) : psi (-t) = -psi t := by simp [psi]

theorem psi_core (t : ℝ) (ht : |t| ≤ 2) : psi t = t := by
  have h : (|t| - 2) / 32 ≤ 0 := by linarith
  simp [psi, step_zero h]

theorem psi_support (t : ℝ) (ht : 34 ≤ |t|) : psi t = 0 := by
  have h : 1 ≤ (|t| - 2) / 32 := by linarith
  simp [psi, step_one h]

theorem psi_hasDerivAt_pos (t : ℝ) (ht : 0 < t) :
    HasDerivAt psi (1 - SmallGap.septicStep ((t - 2) / 32) -
      t / 32 * deriv SmallGap.septicStep ((t - 2) / 32)) t := by
  have hs := ((SepticRegularity.septicStep_contDiff.differentiable (by norm_num))
    ((|t| - 2) / 32)).hasDerivAt.comp t (((hasDerivAt_abs_pos ht).sub_const 2).div_const 32)
  have h := (hasDerivAt_id t).mul (hs.const_sub 1)
  convert h using 1
  dsimp
  rw [abs_of_pos ht]
  ring

theorem psi_hasDerivAt_zero : HasDerivAt psi 1 0 := by
  apply (hasDerivAt_id (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (by norm_num : (-1 : ℝ) < 0),
    eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)] with v hv0 hv1
  exact psi_core v (abs_le.mpr ⟨by linarith, by linarith⟩)

/-- The exact inequalities used to exclude stationary points outside the core. -/
theorem psi_deriv_bounds (t : ℝ) (ht : 0 ≤ t) :
    -t / 4 ≤ deriv psi t ∧ deriv psi t ≤ 1 := by
  rcases eq_or_lt_of_le ht with ht | ht
  · subst t
    rw [psi_hasDerivAt_zero.deriv]
    norm_num
  · rw [(psi_hasDerivAt_pos t ht).deriv]
    have hs := SmallGap.septicStep_range ((t - 2) / 32)
    have hd := SepticRegularity.septicStep_deriv_bounds ((t - 2) / 32)
    have hprod0 : 0 ≤ t / 32 * deriv SmallGap.septicStep ((t - 2) / 32) :=
      mul_nonneg (by positivity) hd.1
    have hprod := mul_le_mul_of_nonneg_left hd.2 (by positivity : 0 ≤ t / 32)
    constructor <;> nlinarith

theorem normal_odd (a s : ℝ) : normal a (-s) = -normal a s := by
  simp only [normal,neg_div,neg_sq,neg_mul]

theorem normal_core (a s : ℝ) (ha : 0 < a) (hs : |s| ≤ a / 4) : normal a s = s := by
  have hd : |s/a|≤1/4 := by
    rw [abs_div,abs_of_pos ha]
    exact (div_le_iff₀ ha).mpr (by linarith)
  have hsq := pow_le_pow_left₀ (abs_nonneg (s/a)) hd 2
  rw [sq_abs] at hsq
  simp only [normal,Real.smoothTransition.zero_of_nonpos (by nlinarith : (16*(s/a)^2-1)/3≤0),sub_zero,mul_one]

theorem normal_support (a s : ℝ) (ha : 0 < a) (hs : a ≤ |s|) : normal a s = 0 := by
  have hd : 1≤|s/a| := by
    rw [abs_div,abs_of_pos ha]
    exact (le_div_iff₀ ha).mpr (by simpa using hs)
  have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hd 2
  rw [sq_abs] at hsq
  simp only [normal,Real.smoothTransition.one_of_one_le (by nlinarith : 1≤(16*(s/a)^2-1)/3),sub_self,mul_zero]

theorem normal_abs_le (a s : ℝ) : |normal a s| ≤ |s| := by
  have h0 := Real.smoothTransition.nonneg ((16*(s/a)^2-1)/3)
  have h1 := Real.smoothTransition.le_one ((16*(s/a)^2-1)/3)
  rw [normal,abs_mul,abs_of_nonneg (by linarith : 0≤1-Real.smoothTransition ((16*(s/a)^2-1)/3))]
  nlinarith [abs_nonneg s]

theorem normal_bounded (a s : ℝ) (ha : 0 < a) : |normal a s| ≤ a := by
  by_cases hs : a ≤ |s|
  · rw [normal_support a s ha hs, abs_zero]
    exact ha.le
  · exact (normal_abs_le a s).trans (le_of_not_ge hs)

/-- Absolute value causes no singularity because the profile is exactly the
identity on a whole neighborhood of zero. -/
theorem psi_contDiff : ContDiff ℝ 3 psi := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  by_cases ht : t = 0
  · subst t
    apply contDiffAt_id.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds (by norm_num : (-1 : ℝ) < 0),
      eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)] with v hv0 hv1
    exact psi_core v (abs_le.mpr ⟨by linarith, by linarith⟩)
  · exact contDiffAt_id.mul (contDiffAt_const.sub
      (SepticRegularity.septicStep_contDiff.contDiffAt.comp t
        (((contDiffAt_abs ht).sub contDiffAt_const).div_const 32)))

theorem normal_contDiff_all (a : ℝ) {k : ℕ∞} : ContDiff ℝ k (normal a) :=
  contDiff_id.mul (contDiff_const.sub (Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul ((contDiff_id.div_const a).pow 2)).sub contDiff_const).div_const 3)))

theorem normal_contDiff (a : ℝ) (_ha : 0 < a) : ContDiff ℝ 3 (normal a) :=
  normal_contDiff_all a

theorem phi_contDiff : ContDiff ℝ 3 phi := by
  have hc : ContDiff ℝ 2 (fun t : ℝ => t * (1 - SmallGap.septicStep (|t| - 1))) := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    by_cases ht : t = 0
    · subst t
      apply contDiffAt_id.congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds (by norm_num : (-1 : ℝ) < 0),
        eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)] with v hv0 hv1
      have hv : |v| - 1 ≤ 0 := by
        have h := abs_le.mpr ⟨hv0.le, hv1.le⟩
        linarith
      simp only [step_zero hv, sub_zero, mul_one, id_eq]
    · exact contDiffAt_id.mul (contDiffAt_const.sub
        ((SepticRegularity.septicStep_contDiff.of_le (by decide : (2 : WithTop ℕ∞) ≤ 3)).contDiffAt.comp t
          ((contDiffAt_abs ht).sub contDiffAt_const)))
  change ContDiff ℝ ((2 : WithTop ℕ∞) + 1) phi
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun t => (phi_hasDerivAt t).differentiableAt, ?_, ?_⟩
  · norm_num
  · have heq : deriv phi = fun t => t * (1 - SmallGap.septicStep (|t| - 1)) := funext phi_deriv
    rw [heq]
    exact hc

theorem phi_deriv_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ deriv phi t := by
  rw [phi_deriv]
  exact mul_nonneg ht (sub_nonneg.mpr (SmallGap.septicStep_range _).2)

theorem phi_deriv_bounded (t : ℝ) : |deriv phi t| ≤ 2 := by
  rw [phi_deriv]
  by_cases ht : 2 ≤ |t|
  · rw [step_one (show 1 ≤ |t| - 1 by linarith)]
    norm_num
  · have hs := SmallGap.septicStep_range (|t| - 1)
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hs.2)]
    have hn := abs_nonneg t
    have hprod := mul_nonneg hn hs.1
    nlinarith

theorem phi_bounded (t : ℝ) : phi t ≤ 2 := by
  by_cases ht : 2 ≤ |t|
  · rw [phi_constant_tail t ht]
    have h := phi_le_quadratic 2
    norm_num at h
    exact h
  · have h := phi_le_quadratic t
    have ha : |t| ≤ 2 := le_of_not_ge ht
    nlinarith [sq_abs t, abs_nonneg t]

theorem phi_deriv_core (t : ℝ) (ht : |t| ≤ 1) : deriv phi t = t := by
  rw [phi_deriv, step_zero (by linarith : |t| - 1 ≤ 0)]
  ring

theorem phi_deriv_odd (t : ℝ) : deriv phi (-t) = -deriv phi t := by
  simp [phi_deriv]

theorem step_deriv_zero_of_one_le (t : ℝ) (ht : 1 ≤ t) :
    deriv SmallGap.septicStep t = 0 := by
  rw [SepticRegularity.septicStep_deriv]
  unfold SepticRegularity.clip SepticRegularity.join
  rw [if_neg (by linarith : ¬t ≤ 0)]
  split_ifs with ht1
  · have heq : t = 1 := le_antisymm ht1 ht
    norm_num [heq, SepticRegularity.d1]
  · rfl

theorem step_deriv_zero_of_nonpos (t : ℝ) (ht : t ≤ 0) :
    deriv SmallGap.septicStep t = 0 := by
  rw [SepticRegularity.septicStep_deriv]
  simp only [SepticRegularity.clip, SepticRegularity.join, if_pos ht]

theorem psi_deriv_core_nonneg (t : ℝ) (hzero : 0 ≤ t) (htwo : t ≤ 2) :
    deriv psi t = 1 := by
  rcases eq_or_lt_of_le hzero with ht | ht
  · subst t
    exact psi_hasDerivAt_zero.deriv
  · rw [(psi_hasDerivAt_pos t ht).deriv]
    have harg : (t - 2) / 32 ≤ 0 := by linarith
    rw [step_zero harg, step_deriv_zero_of_nonpos _ harg]
    ring

theorem psi_deriv_zero_pos (t : ℝ) (ht : 34 ≤ t) : deriv psi t = 0 := by
  rw [(psi_hasDerivAt_pos t (by linarith)).deriv]
  have harg : 1 ≤ (t - 2) / 32 := by linarith
  rw [step_one harg, step_deriv_zero_of_one_le _ harg]
  ring

theorem psi_deriv_even (t : ℝ) : deriv psi (-t) = deriv psi t := by
  have hd := ((psi_contDiff.differentiable (by norm_num)) (-t)).hasDerivAt
  have hc := (hd.comp t (hasDerivAt_neg t)).neg
  have he : HasDerivAt psi (deriv psi (-t)) t := by
    convert hc using 1
    · funext z
      simp only [Function.comp_apply, psi_odd, neg_neg]
    · ring
  exact he.deriv.symm

theorem psi_deriv_zero (t : ℝ) (ht : 34 ≤ |t|) : deriv psi t = 0 := by
  by_cases hsign : 0 ≤ t
  · rw [abs_of_nonneg hsign] at ht
    exact psi_deriv_zero_pos t ht
  · have hneg : t ≤ 0 := le_of_not_ge hsign
    rw [abs_of_nonpos hneg] at ht
    rw [← psi_deriv_even t]
    exact psi_deriv_zero_pos (-t) ht

theorem psi_deriv_core (t : ℝ) (ht : |t| ≤ 2) : deriv psi t = 1 := by
  by_cases hsign : 0 ≤ t
  · exact psi_deriv_core_nonneg t hsign ((le_abs_self t).trans ht)
  · rw [← psi_deriv_even t]
    exact psi_deriv_core_nonneg (-t) (by linarith) ((neg_le_abs t).trans ht)

end Bilevel.SmallGapProfiles
