import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Abel

/-!
# Deterministic proximal transfer

These lemmas prove the paper's transfer inequality from the local subgradient,
Lipschitz and proximal identities stated in the manuscript. They do not assert
the construction or measurability of a proximal search or a stochastic learner.
-/

namespace HeavyTail

section Scalar

theorem correction_quadratic_bound {G R n η t : ℝ}
    (hG : 0 < G) (hR : 0 ≤ R) (hn : 0 < n) (hη : 0 ≤ η)
    (ht : 0 ≤ t) (hstop : G ≤ t ∨ η ≤ R / (G * n)) :
    η * (G * t - t ^ 2) ≤ G * R / (4 * n) := by
  have htarget : 0 ≤ G * R / (4 * n) := by positivity
  rcases hstop with hlarge | hsmall
  · have hq : G * t - t ^ 2 ≤ 0 := by nlinarith [mul_le_mul_of_nonneg_right hlarge ht]
    exact (mul_nonpos_of_nonneg_of_nonpos hη hq).trans htarget
  · have hquad : G * t - t ^ 2 ≤ G ^ 2 / 4 := by nlinarith [sq_nonneg (t - G / 2)]
    have hs : η * (G ^ 2 / 4) ≤ (R / (G * n)) * (G ^ 2 / 4) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    calc
      η * (G * t - t ^ 2) ≤ η * (G ^ 2 / 4) := mul_le_mul_of_nonneg_left hquad hη
      _ ≤ (R / (G * n)) * (G ^ 2 / 4) := hs
      _ = G * R / (4 * n) := by field_simp; ring

theorem quadratic_completion {k G t : ℝ} (hk : 0 < k) :
    G * t - k / 2 * t ^ 2 ≤ G ^ 2 / (2 * k) := by
  apply (le_div_iff₀ (show 0 < 2 * k by positivity)).mpr
  nlinarith [sq_nonneg (k * t - G)]

end Scalar

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem corrected_mean_norm {g a : E} {G : ℝ}
    (hg : ‖g‖ ≤ G) (ha : ‖a‖ ≤ 3 * G) : ‖g + a‖ ≤ 4 * G := by
  calc
    ‖g + a‖ ≤ ‖g‖ + ‖a‖ := norm_add_le _ _
    _ ≤ 4 * G := by linarith

theorem local_composite_subgradient_transfer {f r : E → ℝ} {y w xstar g a : E}
    {G : ℝ} (hg : ‖g‖ ≤ G)
    (hf : f w - f xstar ≤ @inner ℝ E _ g (w - xstar))
    (hr : r y - r xstar ≤ @inner ℝ E _ a (y - xstar))
    (hlip : f y - f w ≤ G * ‖w - y‖) :
    (f y + r y) - (f xstar + r xstar) ≤
      @inner ℝ E _ (g + a) (y - xstar) + 2 * G * ‖w - y‖ := by
  have hcs : @inner ℝ E _ g (w - y) ≤ G * ‖w - y‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hg (norm_nonneg _))
  have hsplit : @inner ℝ E _ g (w - xstar) =
      @inner ℝ E _ g (y - xstar) + @inner ℝ E _ g (w - y) := by
    simp only [inner_sub_right]
    ring
  rw [hsplit] at hf
  simp only [inner_add_left]
  linarith

theorem proximal_inner_correction {z y xstar g a : E} {G η : ℝ}
    (hg : ‖g‖ ≤ G) (hη : 0 ≤ η) (hprox : z - y = η • a) :
    @inner ℝ E _ (g + a) (y - xstar) ≤
      @inner ℝ E _ (g + a) (z - xstar) + η * (G * ‖a‖ - ‖a‖ ^ 2) := by
  have hcs : -(G * ‖a‖) ≤ @inner ℝ E _ g a := by
    have h := (abs_le.mp (abs_real_inner_le_norm g a)).1
    have hmul := mul_le_mul_of_nonneg_right hg (norm_nonneg a)
    linarith
  have hsum : @inner ℝ E _ (g + a) a = @inner ℝ E _ g a + ‖a‖ ^ 2 := by
    rw [inner_add_left, real_inner_self_eq_norm_sq]
  have hsplit : @inner ℝ E _ (g + a) (z - xstar) - @inner ℝ E _ (g + a) (y - xstar) =
      η * @inner ℝ E _ (g + a) a := by
    rw [← inner_sub_right]
    have heq : z - xstar - (y - xstar) = z - y := by abel
    rw [heq, hprox, real_inner_smul_right]
  rw [hsum] at hsplit
  have hm := mul_le_mul_of_nonneg_left hcs hη
  nlinarith

theorem proximal_transfer {f r : E → ℝ} {z y w xstar g a : E}
    {G R n η : ℝ} (hG : 0 < G) (hR : 0 ≤ R) (hn : 0 < n)
    (hη : 0 ≤ η) (hg : ‖g‖ ≤ G)
    (hf : f w - f xstar ≤ @inner ℝ E _ g (w - xstar))
    (hr : r y - r xstar ≤ @inner ℝ E _ a (y - xstar))
    (hlip : f y - f w ≤ G * ‖w - y‖)
    (hprox : z - y = η • a)
    (hstop : G ≤ ‖a‖ ∨ η ≤ R / (G * n))
    (hnear : ‖w - y‖ ≤ R / (8 * n)) :
    (f y + r y) - (f xstar + r xstar) ≤
      @inner ℝ E _ (g + a) (z - xstar) + G * R / (2 * n) := by
  have hlocal := local_composite_subgradient_transfer hg hf hr hlip
  have hcorrection := proximal_inner_correction hg hη hprox (xstar := xstar)
  have hquad := correction_quadratic_bound hG hR hn hη (norm_nonneg a) hstop
  have hnear' := mul_le_mul_of_nonneg_left hnear (show 0 ≤ 2 * G by positivity)
  have hid : 2 * G * (R / (8 * n)) + G * R / (4 * n) = G * R / (2 * n) := by ring
  linarith

omit [InnerProductSpace ℝ E] in
theorem proximal_zero_query_bound {f r : E → ℝ} {y x₁ xstar : E}
    {G D μ η : ℝ} (hη : 0 < η) (hμ : 0 ≤ μ)
    (hinit : ‖x₁ - xstar‖ ≤ D)
    (hf : f y - f xstar ≤ G * ‖y - xstar‖)
    (hprox : r y - r xstar ≤
      (‖x₁ - xstar‖ ^ 2 - ‖y - x₁‖ ^ 2) / (2 * η) -
        (μ + η⁻¹) / 2 * ‖y - xstar‖ ^ 2) :
    (f y + r y) - (f xstar + r xstar) ≤
      D ^ 2 / (2 * η) + G ^ 2 / (2 * (μ + η⁻¹)) := by
  have hk : 0 < μ + η⁻¹ := add_pos_of_nonneg_of_pos hμ (inv_pos.mpr hη)
  have hd : ‖x₁ - xstar‖ ^ 2 - ‖y - x₁‖ ^ 2 ≤ D ^ 2 := by
    nlinarith [norm_nonneg (x₁ - xstar), sq_nonneg ‖y - x₁‖]
  have hdiv := div_le_div_of_nonneg_right hd (show 0 ≤ 2 * η by positivity)
  have hquad := quadratic_completion (G := G) (t := ‖y - xstar‖) hk
  linarith

omit [InnerProductSpace ℝ E] in
theorem proximal_zero_query_convex_cap {f r : E → ℝ} {y x₁ xstar : E}
    {G D : ℝ} (hG : 0 < G) (hD : 0 < D)
    (hinit : ‖x₁ - xstar‖ ≤ D)
    (hf : f y - f xstar ≤ G * ‖y - xstar‖)
    (hprox : r y - r xstar ≤
      (‖x₁ - xstar‖ ^ 2 - ‖y - x₁‖ ^ 2) / (2 * (D / G)) -
        (D / G)⁻¹ / 2 * ‖y - xstar‖ ^ 2) :
    (f y + r y) - (f xstar + r xstar) ≤ G * D := by
  have hp : r y - r xstar ≤
      (‖x₁ - xstar‖ ^ 2 - ‖y - x₁‖ ^ 2) / (2 * (D / G)) -
        (0 + (D / G)⁻¹) / 2 * ‖y - xstar‖ ^ 2 := by simpa using hprox
  have h := proximal_zero_query_bound (div_pos hD hG) (le_refl (0 : ℝ)) hinit hf hp
  have heq : D ^ 2 / (2 * (D / G)) + G ^ 2 / (2 * (0 + (D / G)⁻¹)) = G * D := by
    field_simp; ring
  exact heq ▸ h

end InnerProduct

end HeavyTail

