import SecondOrder.OjaStep

open MeasureTheory
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

/-- The shifted oracle has the stronger quadratic contraction needed for
the Oja potential, not only an operator-norm bound. -/
theorem shiftedHessian_firm {d : ℕ} {B : ℝ} (hB : 0 < B)
    {H : Point d →L[ℝ] Point d} (hH : ‖H‖ ≤ B) (v : Point d) :
    ‖shiftedHessian B H v‖^2 ≤ ⟪shiftedHessian B H v, v⟫_ℝ := by
  have hv : ‖H v‖ ≤ B * ‖v‖ := (H.le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hH (norm_nonneg v))
  have hv2 := pow_le_pow_left₀ (norm_nonneg _) hv 2
  rw [shiftedHessian_rayleigh, shiftedHessian_apply, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, norm_sub_sq_real, norm_smul,
    Real.norm_of_nonneg hB.le, inner_smul_left, conj_trivial, real_inner_comm v (H v)]
  apply (mul_le_mul_left (by positivity : 0 < (2 * B)^2)).mp
  have h2B : 2 * B ≠ 0 := ne_of_gt (by positivity)
  have hc (s : ℝ) : (2 * B)^2 * (s / (2 * B)) = 2 * B * s := by
    field_simp
    ring
  rw [hc, ← mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 h2B), one_mul]
  nlinarith

theorem ojaUpdate_norm_sq {d : ℕ} (η : ℝ) (A : Point d →L[ℝ] Point d) (v : Point d) :
    ‖ojaUpdate η A v‖^2 = ‖v‖^2 + 2 * η * ⟪A v, v⟫_ℝ + η^2 * ‖A v‖^2 := by
  rw [ojaUpdate, norm_add_sq_real, inner_smul_right, real_inner_comm v (A v),
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

theorem ojaUpdate_norm_sq_le {d : ℕ} (η : ℝ) {A : Point d →L[ℝ] Point d}
    {v : Point d} (hA : ‖A v‖^2 ≤ ⟪A v, v⟫_ℝ) :
    ‖ojaUpdate η A v‖^2 ≤ ‖v‖^2 + (2 * η + η^2) * ⟪A v, v⟫_ℝ := by
  rw [ojaUpdate_norm_sq]
  nlinarith [mul_le_mul_of_nonneg_left hA (sq_nonneg η)]

theorem normalizeProbe_rayleigh_scale {d : ℕ} (A : Point d →L[ℝ] Point d) (v : Point d) :
    ‖v‖^2 * ⟪A (normalizeProbe v), normalizeProbe v⟫_ℝ = ⟪A v, v⟫_ℝ := by
  by_cases hv : v = 0
  · simp [hv, normalizeProbe]
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    simp only [normalizeProbe, map_smul, inner_smul_left, inner_smul_right, conj_trivial]
    field_simp
    ring

/-- Deterministic one-step exponential potential inequality. -/
theorem ojaUpdate_norm_sq_exp {d : ℕ} (η : ℝ) {A : Point d →L[ℝ] Point d}
    {v : Point d} (hA : ‖A v‖^2 ≤ ⟪A v, v⟫_ℝ) :
    ‖ojaUpdate η A v‖^2 ≤ ‖v‖^2 * Real.exp
      ((2 * η + η^2) * ⟪A (normalizeProbe v), normalizeProbe v⟫_ℝ) := by
  have he := Real.add_one_le_exp
    ((2 * η + η^2) * ⟪A (normalizeProbe v), normalizeProbe v⟫_ℝ)
  have hm := mul_le_mul_of_nonneg_left he (sq_nonneg ‖v‖)
  have hs := normalizeProbe_rayleigh_scale A v
  have hstep := ojaUpdate_norm_sq_le η hA
  calc
    _ ≤ ‖v‖^2 + (2 * η + η^2) * ⟪A v, v⟫_ℝ := hstep
    _ = ‖v‖^2 * ((2 * η + η^2) *
        ⟪A (normalizeProbe v), normalizeProbe v⟫_ℝ + 1) := by rw [← hs]; ring
    _ ≤ _ := hm

/-- Fourth-moment expansion for a positive contraction, with explicit
constants valid on the learning-rate range used by the concentration proof. -/
theorem ojaUpdate_norm_four_le {d : ℕ} {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1)
    {A : Point d →L[ℝ] Point d} {v : Point d}
    (hA : ‖A v‖^2 ≤ ⟪A v, v⟫_ℝ) (hR : ⟪A v, v⟫_ℝ ≤ ‖v‖^2) :
    ‖ojaUpdate η A v‖^4 ≤ ‖v‖^4 +
      (4 * η + 11 * η^2) * ‖v‖^2 * ⟪A v, v⟫_ℝ := by
  let R := ⟪A v, v⟫_ℝ
  let V := ‖v‖^2
  let c := 2 * η + η^2
  have hR0 : 0 ≤ R := (sq_nonneg _).trans hA
  have hV0 : 0 ≤ V := sq_nonneg _
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hRV : R ≤ V := hR
  have hq := ojaUpdate_norm_sq_le η hA
  have hq2 := pow_le_pow_left₀ (sq_nonneg ‖ojaUpdate η A v‖) hq 2
  have hRR : R^2 ≤ V * R := by nlinarith [mul_le_mul_of_nonneg_right hRV hR0]
  have hη2 : η^2 ≤ η := by nlinarith
  have hη3 : η^3 ≤ η^2 := by nlinarith [mul_le_mul_of_nonneg_left hη2 hη]
  have hη4 : η^4 ≤ η^2 := by nlinarith [pow_le_pow_left₀ (sq_nonneg η) hη2 2]
  have hcoef : 2 * c + c^2 ≤ 4 * η + 11 * η^2 := by dsimp [c]; nlinarith
  have hterm := mul_le_mul_of_nonneg_left hRR (sq_nonneg c)
  have hlast := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hV0 hR0)
  have hV2 : ‖v‖^4 = V^2 := by dsimp [V]; ring
  rw [hV2]
  change ‖ojaUpdate η A v‖^4 ≤ V^2 + (4 * η + 11 * η^2) * V * R
  change (‖ojaUpdate η A v‖^2)^2 ≤ (V + c * R)^2 at hq2
  nlinarith

end
end SecondOrder
