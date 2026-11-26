import RandomizedFO2003.SphereLaw

namespace RandomizedFO2003.Spherical

open MeasureTheory

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def moment (v : E) (k : ℕ) : ℝ :=
  ∫ x, inner (𝕜 := ℝ) v x ^ k ∂sphereLaw E

theorem moment_smul (v : E) (c : ℝ) (k : ℕ) :
    moment E (c • v) k = c ^ k * moment E v k := by
  simp [moment, real_inner_smul_left, mul_pow, integral_const_mul]

theorem moment_radial (v w : E) (hw : ‖w‖ = 1) (k : ℕ) :
    moment E v k = ‖v‖ ^ k * moment E w k := by
  calc
    _ = moment E (‖v‖ • w) k := integral_inner_pow_eq_of_norm_eq E v (‖v‖ • w)
      (by simp [norm_smul, hw]) k
    _ = _ := moment_smul E w ‖v‖ k

variable [Nontrivial E]

theorem integrable_inner_pow (v : E) (k : ℕ) :
    Integrable (fun x => inner (𝕜 := ℝ) v x ^ k) (sphereLaw E) := by
  refine (integrable_const (‖v‖ ^ k)).mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_norm_one E] with x hx
  have hb : |inner (𝕜 := ℝ) v x| ≤ ‖v‖ := by
    simpa [hx] using abs_real_inner_le_norm v x
  simpa [Real.norm_eq_abs, abs_pow] using pow_le_pow_left₀ (abs_nonneg _) hb k

theorem integrable_inner_pow_mul (v w : E) (k l : ℕ) :
    Integrable (fun x => inner (𝕜 := ℝ) v x ^ k * inner (𝕜 := ℝ) w x ^ l)
      (sphereLaw E) := by
  refine (integrable_const (‖v‖ ^ k * ‖w‖ ^ l)).mono'
    (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_norm_one E] with x hx
  have hv : |inner (𝕜 := ℝ) v x| ≤ ‖v‖ := by simpa [hx] using abs_real_inner_le_norm v x
  have hw : |inner (𝕜 := ℝ) w x| ≤ ‖w‖ := by simpa [hx] using abs_real_inner_le_norm w x
  simp only [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hv k)
    (pow_le_pow_left₀ (abs_nonneg _) hw l) (by positivity) (by positivity)

/-- Polarization of fourth moments. Odd mixed terms cancel, so no separate
sign-flip argument or coordinate independence assumption is needed. -/
theorem orthogonal_fourth_mixed (v w : E) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (horth : inner (𝕜 := ℝ) v w = 0) :
    (∫ x, inner (𝕜 := ℝ) v x ^ 2 * inner (𝕜 := ℝ) w x ^ 2 ∂sphereLaw E) =
      moment E v 4 / 3 := by
  have hp : ‖v + w‖ ^ 4 = 4 := by
    have h := norm_add_sq_real v w
    rw [hv, hw, horth] at h
    nlinarith [sq_nonneg (‖v + w‖ ^ 2 - 2)]
  have hm : ‖v - w‖ ^ 4 = 4 := by
    have h := norm_sub_sq_real v w
    rw [hv, hw, horth] at h
    nlinarith [sq_nonneg (‖v - w‖ ^ 2 - 2)]
  have hwv : moment E w 4 = moment E v 4 :=
    integral_inner_pow_eq_of_norm_eq E w v (hw.trans hv.symm) 4
  have hplus := moment_radial E (v + w) v hv 4
  have hminus := moment_radial E (v - w) v hv 4
  rw [hp] at hplus
  rw [hm] at hminus
  have hpolar : moment E (v + w) 4 + moment E (v - w) 4 =
      2 * moment E v 4 + 12 *
        (∫ x, inner (𝕜 := ℝ) v x ^ 2 * inner (𝕜 := ℝ) w x ^ 2 ∂sphereLaw E) +
      2 * moment E w 4 := by
    unfold moment
    rw [← integral_add (integrable_inner_pow E (v + w) 4)
      (integrable_inner_pow E (v - w) 4)]
    have heq : (fun x => inner (𝕜 := ℝ) (v + w) x ^ 4 +
        inner (𝕜 := ℝ) (v - w) x ^ 4) =
        (fun x => (2 : ℝ) * inner (𝕜 := ℝ) v x ^ 4 +
          12 * (inner (𝕜 := ℝ) v x ^ 2 * inner (𝕜 := ℝ) w x ^ 2) +
          2 * inner (𝕜 := ℝ) w x ^ 4) := by
      funext x
      rw [inner_add_left, inner_sub_left]
      ring
    have hint : Integrable (fun x => (2 : ℝ) * inner (𝕜 := ℝ) v x ^ 4 +
        12 * (inner (𝕜 := ℝ) v x ^ 2 * inner (𝕜 := ℝ) w x ^ 2)) (sphereLaw E) :=
      ((integrable_inner_pow E v 4).const_mul 2).add
        ((integrable_inner_pow_mul E v w 2 2).const_mul 12)
    rw [heq, integral_add hint
      ((integrable_inner_pow E w 4).const_mul 2),
      integral_add ((integrable_inner_pow E v 4).const_mul 2)
      ((integrable_inner_pow_mul E v w 2 2).const_mul 12)]
    simp only [integral_const_mul]
  linarith

end RandomizedFO2003.Spherical
