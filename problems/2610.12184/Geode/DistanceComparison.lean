import Geode.Acosh
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Hyperbolic cosine-law comparison

The inverse-cosh law of cosines dominates its Euclidean counterpart. This is
proved from convexity of `w ↦ cosh (sqrt w)` via its positive power series,
including at the endpoint `w = 0`.
-/

namespace Geode

theorem hasSum_cosh_sqrt {x : ℝ} (hx : 0 ≤ x) :
    HasSum (fun n : ℕ => x ^ n / ((2 * n).factorial : ℝ))
      (Real.cosh (Real.sqrt x)) := by
  simpa only [pow_mul, Real.sq_sqrt hx] using Real.hasSum_cosh (Real.sqrt x)

theorem convexOn_cosh_sqrt :
    ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => Real.cosh (Real.sqrt x)) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hm : 0 ≤ a * x + b * y := by
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  apply hasSum_le _ (hasSum_cosh_sqrt hm)
    (((hasSum_cosh_sqrt hx).mul_left a).add ((hasSum_cosh_sqrt hy).mul_left b))
  intro n
  have hp := (convexOn_pow (𝕜 := ℝ) n).2 hx hy ha hb hab
  simp only [smul_eq_mul] at hp
  have hd := div_le_div_of_nonneg_right hp
    (show (0 : ℝ) ≤ ((2 * n).factorial : ℝ) by positivity)
  convert hd using 1
  ring

/-- The scalar comparison holds without sign restrictions on `r` and `s`.
Nonnegative radii are imposed when converting it into a distance inequality. -/
theorem cosh_sqrt_cosine_le {r s c : ℝ} (hc0 : -1 ≤ c) (hc1 : c ≤ 1) :
    Real.cosh (Real.sqrt (r ^ 2 + s ^ 2 - 2 * r * s * c)) ≤
      Real.cosh r * Real.cosh s - Real.sinh r * Real.sinh s * c := by
  have h := convexOn_cosh_sqrt.2 (sq_nonneg (r - s)) (sq_nonneg (r + s))
    (show 0 ≤ (1 + c) / 2 by linarith)
    (show 0 ≤ (1 - c) / 2 by linarith)
    (show (1 + c) / 2 + (1 - c) / 2 = 1 by ring)
  simp only [smul_eq_mul] at h
  have hw : (1 + c) / 2 * (r - s) ^ 2 + (1 - c) / 2 * (r + s) ^ 2 =
      r ^ 2 + s ^ 2 - 2 * r * s * c := by ring
  rw [hw, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
    Real.cosh_abs, Real.cosh_abs, Real.cosh_sub, Real.cosh_add] at h
  nlinarith

theorem hyperbolic_cosine_law_ge_one {r s c : ℝ}
    (hc0 : -1 ≤ c) (hc1 : c ≤ 1) :
    1 ≤ Real.cosh r * Real.cosh s - Real.sinh r * Real.sinh s * c :=
  (Real.one_le_cosh _).trans (cosh_sqrt_cosine_le hc0 hc1)

theorem cosine_law_log_contraction {r s c : ℝ}
    (hc0 : -1 ≤ c) (hc1 : c ≤ 1) :
    Real.sqrt (r ^ 2 + s ^ 2 - 2 * r * s * c) ≤
      arcosh (Real.cosh r * Real.cosh s - Real.sinh r * Real.sinh s * c) := by
  apply (le_arcosh_iff_cosh_le (hyperbolic_cosine_law_ge_one hc0 hc1)
    (Real.sqrt_nonneg _)).mpr
  exact cosh_sqrt_cosine_le hc0 hc1

theorem cosine_expression_nonneg {r s c : ℝ} (hc0 : -1 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ r ^ 2 + s ^ 2 - 2 * r * s * c := by
  have hleft := mul_nonneg (show 0 ≤ 1 + c by linarith) (sq_nonneg (r - s))
  have hright := mul_nonneg (show 0 ≤ 1 - c by linarith) (sq_nonneg (r + s))
  nlinarith

theorem cosine_law_squared_log_contraction {r s c : ℝ}
    (hc0 : -1 ≤ c) (hc1 : c ≤ 1) :
    r ^ 2 + s ^ 2 - 2 * r * s * c ≤
      arcosh (Real.cosh r * Real.cosh s - Real.sinh r * Real.sinh s * c) ^ 2 := by
  have hcomp := cosine_law_log_contraction (r := r) (s := s) hc0 hc1
  have hrad := cosine_expression_nonneg (r := r) (s := s) hc0 hc1
  have hs := Real.sqrt_nonneg (r ^ 2 + s ^ 2 - 2 * r * s * c)
  have ha := arcosh_nonneg
    (Real.cosh r * Real.cosh s - Real.sinh r * Real.sinh s * c)
  nlinarith [Real.sq_sqrt hrad]

end Geode
