import NCConcave16991.LocalizationScalar
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Certified numerical derivative bound for the actual exponential step

This proves the explicit step derivative and the paper's global bound 8.
The estimate uses the monotonicity of `u² exp(2-u)` on `[2,∞)`, so there
is no assumed scalar-derivative certificate or numerical sampling.
-/

namespace NCConcave16991.LocalizationStep

open Set
open scoped ContDiff Topology

theorem glue_hasDerivAt (t : ℝ) :
    HasDerivAt expNegInvGlue (t⁻¹ ^ 2 * expNegInvGlue t) t := by
  simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) t

theorem step_hasDerivAt (t : ℝ) :
    HasDerivAt Real.smoothTransition
      (Real.smoothTransition t * (1 - Real.smoothTransition t) *
        (t⁻¹ ^ 2 + (1 - t)⁻¹ ^ 2)) t := by
  have ha := glue_hasDerivAt t
  have hb := (glue_hasDerivAt (1 - t)).comp t ((hasDerivAt_const t 1).sub (hasDerivAt_id t))
  have hh := ha.div (ha.add hb) (ne_of_gt (Real.smoothTransition.pos_denom t))
  refine hh.congr_deriv ?_
  unfold Real.smoothTransition
  dsimp
  generalize t⁻¹ = u
  generalize (1 - t)⁻¹ = v
  field_simp [ne_of_gt (Real.smoothTransition.pos_denom t)]
  ring

theorem step_deriv (t : ℝ) :
    deriv Real.smoothTransition t = Real.smoothTransition t * (1 - Real.smoothTransition t) *
      (t⁻¹ ^ 2 + (1 - t)⁻¹ ^ 2) := (step_hasDerivAt t).deriv

theorem step_symmetry (t : ℝ) : Real.smoothTransition t + Real.smoothTransition (1 - t) = 1 := by
  unfold Real.smoothTransition
  rw [show 1 - (1 - t) = t by ring, add_comm (expNegInvGlue (1 - t))]
  rw [← add_div, div_self (ne_of_gt (Real.smoothTransition.pos_denom t))]

theorem step_deriv_symmetry (t : ℝ) : deriv Real.smoothTransition (1 - t) =
    deriv Real.smoothTransition t := by
  rw [step_deriv, step_deriv, show 1 - (1 - t) = t by ring]
  have hs := step_symmetry t
  have he : Real.smoothTransition (1 - t) = 1 - Real.smoothTransition t := by linarith
  rw [he]
  ring

theorem step_integral_half : (∫ t in (0 : ℝ)..1, Real.smoothTransition t) = 1 / 2 := by
  have hc := Real.smoothTransition.continuous
  have hr : (∫ t in (0 : ℝ)..1, Real.smoothTransition (1 - t)) =
      ∫ t in (0 : ℝ)..1, Real.smoothTransition t := by
    simp only [intervalIntegral.integral_comp_sub_left, sub_self, sub_zero]
  have hcomp : Continuous (fun t : ℝ => Real.smoothTransition (1 - t)) :=
    hc.comp (continuous_const.sub continuous_id)
  have hh : (∫ t in (0 : ℝ)..1,
      (Real.smoothTransition t + Real.smoothTransition (1 - t))) = 1 := by
    calc
      _ = ∫ _ in (0 : ℝ)..1, (1 : ℝ) :=
        intervalIntegral.integral_congr (fun t _ => step_symmetry t)
      _ = 1 := by simp
  rw [intervalIntegral.integral_add (hc.intervalIntegrable 0 1)
    (hcomp.intervalIntegrable 0 1), hr] at hh
  linarith

/-- The constructed integral profile equals the source's transition formula. -/
theorem radialLength_transition {C : ℝ} (hC : 0 < C) (r : ℝ) :
    LocalizationScalar.radialLength C r = C + C *
      (∫ v in (0 : ℝ)..((r - C) / C), (1 - Real.smoothTransition v)) := by
  have hc := (LocalizationScalar.radialSpeed_contDiff C).continuous
  have hh := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0 C) (hc.intervalIntegrable C r)
  have hid := LocalizationScalar.radialLength_identity hC (le_refl C)
  change (∫ s in (0 : ℝ)..C, LocalizationScalar.radialSpeed C s) = C at hid
  have hchange : (∫ s in C..r, LocalizationScalar.radialSpeed C s) =
      C * (∫ v in (0 : ℝ)..((r - C) / C), (1 - Real.smoothTransition v)) := by
    calc
      _ = ∫ s in C..r, (1 - Real.smoothTransition (s / C - 1)) := by
        apply intervalIntegral.integral_congr
        intro s _
        unfold LocalizationScalar.radialSpeed
        rw [sub_div, div_self hC.ne']
      _ = _ := by
        rw [intervalIntegral.integral_comp_div_sub (fun v => 1 - Real.smoothTransition v) hC.ne' 1]
        simp only [div_self hC.ne', sub_self, smul_eq_mul, sub_div]
  change (∫ s in (0 : ℝ)..r, LocalizationScalar.radialSpeed C s) = _
  rw [hid, hchange] at hh
  exact hh.symm

/-- Exact outer plateau `3C/2` from the step symmetry, as in the source. -/
theorem radialLength_plateau {C r : ℝ} (hC : 0 < C) (hr : 2 * C ≤ r) :
    LocalizationScalar.radialLength C r = 3 * C / 2 := by
  rw [LocalizationScalar.radialLength_constant hC hr, radialLength_transition hC]
  have harg : (2 * C - C) / C = 1 := by field_simp; ring
  rw [harg, intervalIntegral.integral_sub (continuous_const.intervalIntegrable 0 1)
    (Real.smoothTransition.continuous.intervalIntegrable 0 1), step_integral_half]
  simp
  ring

theorem sq_exp_bound {u : ℝ} (hu : 2 ≤ u) : u ^ 2 * Real.exp (2 - u) ≤ 4 := by
  let f : ℝ → ℝ := fun x => x ^ 2 * Real.exp (2 - x)
  have hd (x : ℝ) : HasDerivAt f ((2 * x - x ^ 2) * Real.exp (2 - x)) x := by
    have hh := ((hasDerivAt_id x).pow 2).mul
      (((hasDerivAt_const x 2).sub (hasDerivAt_id x)).exp)
    change HasDerivAt f _ x at hh
    exact hh.congr_deriv (by dsimp; ring)
  have hanti : AntitoneOn f (Ici 2) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 2)
    · exact (continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)).continuousOn
    · exact (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
    · intro x hx
      rw [(hd x).deriv]
      have hx2 : 2 ≤ x := le_of_lt (by simpa using hx)
      exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (Real.exp_pos _).le
  have hh := hanti (show (2 : ℝ) ∈ Ici 2 from by simp) hu hu
  norm_num [f] at hh ⊢
  exact hh

theorem step_le_exp {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2) :
    Real.smoothTransition t ≤ Real.exp (2 - t⁻¹) := by
  have h1 : 0 < 1 - t := by linarith
  have ha : 0 ≤ Real.exp (-1 / t) := (Real.exp_pos _).le
  have hb : 0 < Real.exp (-1 / (1 - t)) := Real.exp_pos _
  have hrec : (1 - t)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ h1]
    linarith
  calc
    Real.smoothTransition t = Real.exp (-1 / t) /
        (Real.exp (-1 / t) + Real.exp (-1 / (1 - t))) := by
      simp [Real.smoothTransition, expNegInvGlue, not_le.mpr ht, not_le.mpr h1,
        one_div, neg_div]
    _ ≤ Real.exp (-1 / t) / Real.exp (-1 / (1 - t)) :=
      div_le_div_of_nonneg_left ha hb (le_add_of_nonneg_left ha)
    _ = Real.exp ((1 - t)⁻¹ - t⁻¹) := by
      rw [← Real.exp_sub]
      congr 1
      simp only [neg_div, one_div]
      ring
    _ ≤ Real.exp (2 - t⁻¹) := Real.exp_le_exp.mpr (by linarith)

theorem step_deriv_le_eight_half {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2) :
    deriv Real.smoothTransition t ≤ 8 := by
  have h1 : 0 < 1 - t := by linarith
  have htinv : 2 ≤ t⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ ht]
    linarith
  have h1inv : (1 - t)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ h1]
    linarith
  have h1sq : (1 - t)⁻¹ ^ 2 ≤ 4 := by
    have hnon := inv_nonneg.mpr h1.le
    nlinarith
  have hstep0 := Real.smoothTransition.nonneg t
  have hstep1 := Real.smoothTransition.le_one t
  have hcoeff : Real.smoothTransition t * (1 - Real.smoothTransition t) ≤
      Real.exp (2 - t⁻¹) := by
    have hh := step_le_exp ht ht2
    nlinarith [sq_nonneg (Real.smoothTransition t)]
  have hexp1 : Real.exp (2 - t⁻¹) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (show 2 - t⁻¹ ≤ 0 by linarith)
  have hs := sq_exp_bound htinv
  rw [step_deriv]
  have hA := mul_le_mul_of_nonneg_right hcoeff
    (show 0 ≤ t⁻¹ ^ 2 + (1 - t)⁻¹ ^ 2 by positivity)
  have hB := mul_le_mul_of_nonneg_left h1sq (Real.exp_pos (2 - t⁻¹)).le
  nlinarith

/-- Global numerical first-derivative estimate for the actual exponential
step used by Appendix E, including both flat endpoints. -/
theorem step_deriv_bounds (t : ℝ) : 0 ≤ deriv Real.smoothTransition t ∧
    deriv Real.smoothTransition t ≤ 8 := by
  constructor
  · exact Real.smoothTransition.monotone.deriv_nonneg
  · by_cases ht0 : t ≤ 0
    · rw [step_deriv, Real.smoothTransition.zero_of_nonpos ht0]
      norm_num
    · by_cases ht1 : 1 ≤ t
      · rw [step_deriv, Real.smoothTransition.one_of_one_le ht1]
        norm_num
      · by_cases hhalf : t ≤ 1 / 2
        · exact step_deriv_le_eight_half (lt_of_not_ge ht0) hhalf
        · rw [← step_deriv_symmetry t]
          exact step_deriv_le_eight_half (by linarith) (by linarith)

theorem radialSpeed_hasDerivAt (C r : ℝ) :
    HasDerivAt (LocalizationScalar.radialSpeed C)
      (-deriv Real.smoothTransition ((r - C) / C) / C) r := by
  have hh := (step_hasDerivAt ((r - C) / C)).comp r
    (((hasDerivAt_id r).sub_const C).div_const C)
  convert (hasDerivAt_const r 1).sub hh using 1
  · rfl
  · rw [← step_deriv]
    ring

/-- The actual integral radial profile has the paper's `8/C` second
derivative bound; the bound is derived from the explicit exponential step. -/
theorem radialLength_second_deriv_bound {C : ℝ} (hC : 0 < C) (r : ℝ) :
    |deriv (deriv (LocalizationScalar.radialLength C)) r| ≤ 8 / C := by
  rw [LocalizationScalar.radialLength_deriv, (radialSpeed_hasDerivAt C r).deriv,
    abs_div, abs_neg, abs_of_pos hC,
    abs_of_nonneg (step_deriv_bounds ((r - C) / C)).1]
  exact div_le_div_of_nonneg_right (step_deriv_bounds _).2 hC.le

end NCConcave16991.LocalizationStep
