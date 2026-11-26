import SecondOrder.OjaRunMoments

open MeasureTheory Filter
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

/-- A lower-tail bound from a mean lower bound and a second-moment upper
bound. The reference a need not equal the actual mean. -/
theorem lower_tail_of_moment_bounds {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {a b : ℝ}
    (hX : Integrable X μ) (hX2 : Integrable (fun w => X w ^ 2) μ)
    (ha : 0 < a) (hmean : a ≤ ∫ w, X w ∂μ) (hmoment : (∫ w, X w ^ 2 ∂μ) ≤ b) :
    μ {w | X w ≤ a / 2} ≤ ENNReal.ofReal (4 * (b / a^2 - 1)) := by
  have he (w : Ω) : (X w - a)^2 = X w ^ 2 - (2 * a) * X w + a^2 := by ring
  have hi : Integrable (fun w => (X w - a)^2) μ := by
    simp_rw [he]
    exact (hX2.sub (hX.const_mul (2 * a))).add (integrable_const _)
  have hint : (∫ w, (X w - a)^2 ∂μ) ≤ b - a^2 := by
    simp_rw [he]
    have hdiff : Integrable (fun w => X w ^ 2 - (2 * a) * X w) μ :=
      hX2.sub (hX.const_mul (2 * a))
    rw [integral_add hdiff (integrable_const (a^2)),
      integral_sub hX2 (hX.const_mul (2 * a)), integral_const_mul]
    simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hmean ha.le]
  have hden : 0 < (a / 2)^2 := sq_pos_of_pos (by positivity)
  have hb := (hi.div_const ((a / 2)^2)).measure_le_integral
    (Eventually.of_forall (fun w => div_nonneg (sq_nonneg _) hden.le))
    (s := {w | X w ≤ a / 2}) (fun w hw => by
      apply (le_div_iff₀ hden).mpr
      have hs : (a / 2)^2 ≤ (a - X w)^2 :=
        pow_le_pow_left₀ (by positivity) (by dsimp at hw; linarith) 2
      nlinarith)
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  rw [integral_div]
  calc
    _ ≤ (b - a^2) / (a / 2)^2 := div_le_div_of_nonneg_right hint hden.le
    _ = _ := by field_simp; ring

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- Growth of the actual random product from a unit eigenvector of the mean.
This is an analytic auxiliary experiment, not an oracle initialization that
is allowed to know the population eigenvector. -/
theorem CommonLoss.ojaRawRun_growth_lower_tail (h : CommonLoss μ P ν F f)
    {η ℓ : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (hℓ0 : 0 ≤ ℓ) (x v : Point d)
    (hℓ : ∀ u, ⟪shiftedHessian (eigenHessianBound P) (hessian F x) u, u⟫_ℝ ≤ ℓ * ‖u‖^2)
    (hv : shiftedHessian (eigenHessianBound P) (hessian F x) v = ℓ • v)
    (hv1 : ‖v‖ = 1) (N : ℕ) :
    drawsLaw μ N {w | ‖ojaRawRun P f η x v N w‖^2 ≤ (1 + η * ℓ)^(2 * N) / 2} ≤
      ENNReal.ofReal (4 * ((1 + (4 * η + 11 * η^2) * ℓ)^N /
        ((1 + η * ℓ)^(2 * N))^2 - 1)) := by
  have hi2 := h.ojaRawRun_norm_pow_integrable hη x v N 2
  have hi4 : Integrable (fun w => (‖ojaRawRun P f η x v N w‖^2)^2) (drawsLaw μ N) := by
    simpa only [← pow_mul] using h.ojaRawRun_norm_pow_integrable hη x v N 4
  have hm := h.ojaRawRun_fourth_moment hη hη1 hℓ0 x v hℓ N
  rw [hv1, one_pow, mul_one] at hm
  exact lower_tail_of_moment_bounds hi2 hi4 (by positivity)
    (h.ojaRawRun_second_moment_lower hη x v hv hv1 N)
    (by simpa only [← pow_mul] using hm)

end
end SecondOrder
