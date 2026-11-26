import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

/-! A finite Taylor upper inequality derived from the actual second derivative. -/
namespace Geode

theorem finite_taylor_upper (f g h : ℝ → ℝ) (C : ℝ)
    (hf : ∀ t, HasDerivAt f (g t) t) (hg : ∀ t, HasDerivAt g (h t) t)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, h t ≤ C) :
    f 1 ≤ f 0 + g 0 + C / 2 := by
  let q : ℝ → ℝ := fun t => C * t ^ 2 / 2 - f t
  have hq : ∀ t, HasDerivAt q (C * t - g t) t := by
    intro t
    have hd := (((hasDerivAt_id t).pow 2).const_mul C).div_const 2
    convert hd.sub (hf t) using 1
    simp only [id_eq]
    ring
  have hq' : ∀ t, HasDerivAt (fun t => C * t - g t) (C - h t) t := by
    intro t
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul C).sub (hg t)
  have hc : ConvexOn ℝ (Set.Icc 0 1) q := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
      ((continuous_iff_continuousAt.mpr fun t => (hq t).continuousAt).continuousOn)
      (fun t _ => (hq t).hasDerivWithinAt)
      (fun t _ => (hq' t).hasDerivWithinAt)
    intro t ht
    exact sub_nonneg.mpr (hbound t (interior_subset ht))
  have hs := hc.le_slope_of_hasDerivAt (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1) (by norm_num : (0 : ℝ) < 1) (hq 0)
  norm_num [q, slope] at hs
  linarith

end Geode
