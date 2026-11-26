import Geode.Acosh
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Inverse-cosh convexity from the distance differential inequality

The hypotheses below describe actual first and second derivatives of a scalar
function. They are discharged separately by the Lorentz geometry of pairs of
geodesics. Positive regularization handles points at which the distance is zero.
-/

namespace Geode

open Set Filter
open scoped Topology

theorem regularized_distance_gram {a b c δ : ℝ} (ha : 1 ≤ a) (hc : 0 ≤ c)
    (hδ : 0 ≤ δ) (hgram : a * b ^ 2 ≤ (a ^ 2 - 1) * c) :
    (a + δ) * b ^ 2 ≤ ((a + δ) ^ 2 - 1) * c := by
  have ha0 : 0 < a := by linarith
  have hprod : 0 ≤ a * (a * c - b ^ 2) := by nlinarith
  have hsimple : b ^ 2 ≤ a * c := by
    have h := nonneg_of_mul_nonneg_right hprod ha0
    linarith
  have hδsimple := mul_nonneg hδ (sub_nonneg.mpr hsimple)
  have hδsq := mul_nonneg (sq_nonneg δ) hc
  have hcross := mul_nonneg (mul_nonneg hδ ha0.le) hc
  nlinarith

theorem arcosh_second_coefficient_nonneg {a b c : ℝ} (ha : 1 < a)
    (hgram : a * b ^ 2 ≤ (a ^ 2 - 1) * c) :
    0 ≤ (-a / Real.sqrt (a ^ 2 - 1) ^ 3 * b) * b +
      (Real.sqrt (a ^ 2 - 1))⁻¹ * c := by
  have hrad : 0 < a ^ 2 - 1 := by nlinarith
  let s := Real.sqrt (a ^ 2 - 1)
  have hs : 0 < s := Real.sqrt_pos.mpr hrad
  have hsq : s ^ 2 = a ^ 2 - 1 := Real.sq_sqrt hrad.le
  change 0 ≤ (-a / s ^ 3 * b) * b + s⁻¹ * c
  have hid : (-a / s ^ 3 * b) * b + s⁻¹ * c =
      ((a ^ 2 - 1) * c - a * b ^ 2) / s ^ 3 := by
    rw [← hsq]
    field_simp
    ring
  rw [hid]
  exact div_nonneg (sub_nonneg.mpr hgram) (pow_nonneg hs.le 3)

theorem convexOn_arcosh_regularized (F G H : ℝ → ℝ)
    (hF : ∀ t, HasDerivAt F (G t) t)
    (hG : ∀ t, HasDerivAt G (H t) t)
    (hvalue : ∀ t, 1 ≤ F t) (hsecond : ∀ t, 0 ≤ H t)
    (hgram : ∀ t, F t * G t ^ 2 ≤ (F t ^ 2 - 1) * H t)
    {δ : ℝ} (hδ : 0 < δ) :
    ConvexOn ℝ univ (fun t => arcosh (F t + δ)) := by
  let f₁ : ℝ → ℝ := fun t => (Real.sqrt ((F t + δ) ^ 2 - 1))⁻¹ * G t
  let f₂ : ℝ → ℝ := fun t =>
    (-(F t + δ) / Real.sqrt ((F t + δ) ^ 2 - 1) ^ 3 * G t) * G t +
      (Real.sqrt ((F t + δ) ^ 2 - 1))⁻¹ * H t
  have hlarge : ∀ t, 1 < F t + δ := fun t => by linarith [hvalue t]
  have hd₁ : ∀ t, HasDerivAt (fun t => arcosh (F t + δ)) (f₁ t) t := by
    intro t
    have h := (hasDerivAt_arcosh (hlarge t)).comp t ((hF t).add_const δ)
    exact h
  have hd₂ : ∀ t, HasDerivAt f₁ (f₂ t) t := by
    intro t
    exact ((hasDerivAt_arcosh_slope (hlarge t)).comp t ((hF t).add_const δ)).mul (hG t)
  refine convexOn_of_hasDerivWithinAt2_nonneg convex_univ
    ((continuous_iff_continuousAt.mpr fun t => (hd₁ t).continuousAt).continuousOn)
    (fun t _ => (hd₁ t).hasDerivWithinAt)
    (fun t _ => (hd₂ t).hasDerivWithinAt) ?_
  intro t _
  exact arcosh_second_coefficient_nonneg (hlarge t)
    (regularized_distance_gram (hvalue t) (hsecond t) hδ.le (hgram t))

/-- The scalar differential inequality proves convexity even where `F = 1`,
without assuming twice differentiability of `arcosh ∘ F` at such points. -/
theorem convexOn_arcosh_of_distance_gram (F G H : ℝ → ℝ)
    (hF : ∀ t, HasDerivAt F (G t) t)
    (hG : ∀ t, HasDerivAt G (H t) t)
    (hvalue : ∀ t, 1 ≤ F t) (hsecond : ∀ t, 0 ≤ H t)
    (hgram : ∀ t, F t * G t ^ 2 ≤ (F t ^ 2 - 1) * H t) :
    ConvexOn ℝ univ (fun t => arcosh (F t)) := by
  have hlim (v : ℝ) :
      Tendsto (fun n : ℕ => arcosh (v + 1 / ((n : ℝ) + 1))) atTop (𝓝 (arcosh v)) := by
    apply continuous_arcosh.continuousAt.tendsto.comp
    simpa only [add_zero] using
      (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => v + 1 / ((n : ℝ) + 1)) atTop (𝓝 (v + 0)))
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  apply le_of_tendsto_of_tendsto' (hlim (F (a * x + b * y)))
    ((tendsto_const_nhds.mul (hlim (F x))).add (tendsto_const_nhds.mul (hlim (F y))))
  intro n
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hconv := convexOn_arcosh_regularized F G H hF hG hvalue hsecond hgram hpos
  simpa only [smul_eq_mul] using hconv.2 (mem_univ x) (mem_univ y) ha hb hab

end Geode
