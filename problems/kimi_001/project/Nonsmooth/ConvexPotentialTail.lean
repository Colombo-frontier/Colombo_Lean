import Nonsmooth.StrongPotentialTails
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem convex_score_tangent (U s : ℝ → ℝ) (hs : Continuous s)
    (hd : ∀ x, HasDerivAt U (s x) x) (hmono : Monotone s) (a x : ℝ) :
    U a + s a * (x - a) ≤ U x := by
  have hd' (t : ℝ) : HasDerivAt (fun t => U (a + t)) (s (a + t)) t := by
    simpa only [Function.comp_def, mul_one] using
      (hd (a + t)).comp t ((hasDerivAt_id t).const_add a)
  have hm' : Monotone (fun t => s (a + t) - 0 * t) := by
    intro t v htv
    simpa only [zero_mul, sub_zero, add_comm] using hmono (add_le_add_left htv a)
  have he := strong_potential_quadratic_lower (fun t => U (a + t))
    (fun t => s (a + t)) (hs.comp (continuous_const.add continuous_id)) hd' hm' (x - a)
  simpa only [add_zero, zero_div, zero_mul, add_sub_cancel] using he

/-- A positive boundary score bounds the complete right tail by the tangent
exponential. This is an unnormalized density statement. -/
theorem convex_potential_right_tail (U s : ℝ → ℝ) (hs : Continuous s)
    (hd : ∀ x, HasDerivAt U (s x) x) (hmono : Monotone s)
    (hi : Integrable (fun x => Real.exp (-U x))) {b : ℝ} (hb : 0 < s b) :
    (∫ x in Ioi b, Real.exp (-U x)) ≤ Real.exp (-U b) / s b := by
  let C := Real.exp (-U b + s b * b)
  have he : IntegrableOn (fun x => C * Real.exp ((-s b) * x)) (Ioi b) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hb) b).const_mul C
  have hle : (∫ x in Ioi b, Real.exp (-U x)) ≤
      ∫ x in Ioi b, C * Real.exp ((-s b) * x) := by
    apply integral_mono_ae hi.integrableOn he
    apply Eventually.of_forall
    intro x
    dsimp only [C]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ht := convex_score_tangent U s hs hd hmono b x
    nlinarith
  have hc : C * Real.exp ((-s b) * b) = Real.exp (-U b) := by
    dsimp only [C]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hb), neg_div_neg_eq,
    ← mul_div_assoc, hc] at hle
  exact hle

theorem convex_potential_left_tail (U s : ℝ → ℝ) (hs : Continuous s)
    (hd : ∀ x, HasDerivAt U (s x) x) (hmono : Monotone s)
    (hi : Integrable (fun x => Real.exp (-U x))) {a : ℝ} (ha : s a < 0) :
    (∫ x in Iic a, Real.exp (-U x)) ≤ Real.exp (-U a) / (-s a) := by
  let C := Real.exp (-U a + s a * a)
  have he : IntegrableOn (fun x => C * Real.exp ((-s a) * x)) (Iic a) :=
    (integrableOn_exp_mul_Iic (neg_pos.mpr ha) a).const_mul C
  have hle : (∫ x in Iic a, Real.exp (-U x)) ≤
      ∫ x in Iic a, C * Real.exp ((-s a) * x) := by
    apply integral_mono_ae hi.integrableOn he
    apply Eventually.of_forall
    intro x
    dsimp only [C]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ht := convex_score_tangent U s hs hd hmono a x
    nlinarith
  have hc : C * Real.exp ((-s a) * a) = Real.exp (-U a) := by
    dsimp only [C]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [integral_const_mul, integral_exp_mul_Iic (neg_pos.mpr ha),
    ← mul_div_assoc, hc] at hle
  exact hle

theorem convex_potential_segment_lower_right (U s : ℝ → ℝ) (hs : Continuous s)
    (hd : ∀ x, HasDerivAt U (s x) x) (hmono : Monotone s)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ s a) :
    (b - a) * Real.exp (-U b) ≤ ∫ x in a..b, Real.exp (-U x) := by
  have hU : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have he := intervalIntegral.integral_mono_on (μ := volume) hab
    (continuous_const.intervalIntegrable a b)
    ((Real.continuous_exp.comp hU.neg).intervalIntegrable a b)
    (f := fun _ => Real.exp (-U b)) (g := fun x => Real.exp (-U x)) (by
      intro x hx
      apply Real.exp_le_exp.mpr
      have ht := convex_score_tangent U s hs hd hmono x b
      have hst : 0 ≤ s x := ha.trans (hmono hx.1)
      have hm := mul_nonneg hst (sub_nonneg.mpr hx.2)
      linarith)
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using he

theorem convex_potential_segment_lower_left (U s : ℝ → ℝ) (hs : Continuous s)
    (hd : ∀ x, HasDerivAt U (s x) x) (hmono : Monotone s)
    {a b : ℝ} (hab : a ≤ b) (hb : s b ≤ 0) :
    (b - a) * Real.exp (-U a) ≤ ∫ x in a..b, Real.exp (-U x) := by
  have hU : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have he := intervalIntegral.integral_mono_on (μ := volume) hab
    (continuous_const.intervalIntegrable a b)
    ((Real.continuous_exp.comp hU.neg).intervalIntegrable a b)
    (f := fun _ => Real.exp (-U a)) (g := fun x => Real.exp (-U x)) (by
      intro x hx
      apply Real.exp_le_exp.mpr
      have ht := convex_score_tangent U s hs hd hmono x a
      have hst : s x ≤ 0 := (hmono hx.2).trans hb
      have hm := mul_nonneg_of_nonpos_of_nonpos hst (sub_nonpos.mpr hx.1)
      linarith)
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using he

theorem convex_potential_right_tail_le_twice_segment (U s : ℝ → ℝ) (hs : Continuous s)
    (hd : ∀ x, HasDerivAt U (s x) x) (hmono : Monotone s)
    (hi : Integrable (fun x => Real.exp (-U x))) {a b : ℝ}
    (hab : a < b) (ha : 0 ≤ s a) (hsize : 1 ≤ (b - a) * s b) :
    (∫ x in Ioi a, Real.exp (-U x)) ≤ 2 * (∫ x in a..b, Real.exp (-U x)) := by
  have hb : 0 < s b := by nlinarith [sub_pos.mpr hab]
  have ht := convex_potential_right_tail U s hs hd hmono hi hb
  have hl := convex_potential_segment_lower_right U s hs hd hmono hab.le ha
  have hdiv : Real.exp (-U b) / s b ≤ (b - a) * Real.exp (-U b) := by
    apply (div_le_iff₀ hb).mpr
    nlinarith [mul_le_mul_of_nonneg_right hsize (Real.exp_pos (-U b)).le]
  have hsplit : (∫ x in Ioi a, Real.exp (-U x)) =
      (∫ x in a..b, Real.exp (-U x)) + ∫ x in Ioi b, Real.exp (-U x) := by
    rw [← Ioc_union_Ioi_eq_Ioi hab.le,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hi.integrableOn hi.integrableOn,
      intervalIntegral.integral_of_le hab.le]
  linarith

theorem convex_potential_left_tail_le_twice_segment (U s : ℝ → ℝ) (hs : Continuous s)
    (hd : ∀ x, HasDerivAt U (s x) x) (hmono : Monotone s)
    (hi : Integrable (fun x => Real.exp (-U x))) {a b : ℝ}
    (hab : a < b) (hb : s b ≤ 0) (hsize : 1 ≤ (b - a) * (-s a)) :
    (∫ x in Iic b, Real.exp (-U x)) ≤ 2 * (∫ x in a..b, Real.exp (-U x)) := by
  have ha : s a < 0 := by nlinarith [sub_pos.mpr hab]
  have ht := convex_potential_left_tail U s hs hd hmono hi ha
  have hl := convex_potential_segment_lower_left U s hs hd hmono hab.le hb
  have hdiv : Real.exp (-U a) / (-s a) ≤ (b - a) * Real.exp (-U a) := by
    apply (div_le_iff₀ (neg_pos.mpr ha)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hsize (Real.exp_pos (-U a)).le]
  have hsplit := intervalIntegral.integral_Iic_sub_Iic
    (a := a) (b := b) hi.integrableOn hi.integrableOn
  linarith

end
end Nonsmooth
