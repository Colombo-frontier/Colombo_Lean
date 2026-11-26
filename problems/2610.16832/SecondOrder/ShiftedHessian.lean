import SecondOrder.HessianSymmetry

open MeasureTheory
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

/-- Shift a Hessian with norm at most B to a positive contraction. -/
def shiftedHessian {d : ℕ} (B : ℝ) (H : Point d →L[ℝ] Point d) :
    Point d →L[ℝ] Point d :=
  (2 * B)⁻¹ • (B • ContinuousLinearMap.id ℝ (Point d) - H)

theorem shiftedHessian_apply {d : ℕ} (B : ℝ) (H : Point d →L[ℝ] Point d)
    (v : Point d) : shiftedHessian B H v = (2 * B)⁻¹ • (B • v - H v) := rfl

theorem shiftedHessian_symmetric {d : ℕ} (B : ℝ) {H : Point d →L[ℝ] Point d}
    (hH : H.toLinearMap.IsSymmetric) : (shiftedHessian B H).toLinearMap.IsSymmetric := by
  intro u v
  change ⟪shiftedHessian B H u, v⟫_ℝ = ⟪u, shiftedHessian B H v⟫_ℝ
  simp only [shiftedHessian_apply, inner_smul_left, inner_smul_right, inner_sub_left,
    inner_sub_right, conj_trivial]
  rw [hH.apply_clm]

theorem shiftedHessian_rayleigh {d : ℕ} (B : ℝ) (H : Point d →L[ℝ] Point d)
    (v : Point d) :
    ⟪shiftedHessian B H v, v⟫_ℝ = (B * ‖v‖^2 - ⟪H v, v⟫_ℝ) / (2 * B) := by
  simp only [shiftedHessian_apply, inner_smul_left, inner_sub_left, conj_trivial,
    real_inner_self_eq_norm_sq]
  ring

theorem rayleigh_abs_le_of_norm_le {d : ℕ} {B : ℝ} {H : Point d →L[ℝ] Point d}
    (hH : ‖H‖ ≤ B) (v : Point d) : |⟪H v, v⟫_ℝ| ≤ B * ‖v‖^2 := by
  calc
    _ ≤ ‖H v‖ * ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (H v) v
    _ ≤ (‖H‖ * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right (H.le_opNorm v) (norm_nonneg _)
    _ ≤ (B * ‖v‖) * ‖v‖ := by gcongr
    _ = _ := by ring

theorem shiftedHessian_rayleigh_bounds {d : ℕ} {B : ℝ}
    (hB : 0 < B) {H : Point d →L[ℝ] Point d} (hH : ‖H‖ ≤ B) (v : Point d) :
    0 ≤ ⟪shiftedHessian B H v, v⟫_ℝ ∧ ⟪shiftedHessian B H v, v⟫_ℝ ≤ ‖v‖^2 := by
  have hr := (abs_le.mp (rayleigh_abs_le_of_norm_le hH v))
  rw [shiftedHessian_rayleigh]
  constructor
  · exact div_nonneg (sub_nonneg.mpr hr.2) (by positivity)
  · apply (div_le_iff₀ (by positivity : 0 < 2 * B)).mpr
    nlinarith [hr.1]

theorem shiftedHessian_norm_le_one {d : ℕ} {B : ℝ}
    (hB : 0 < B) {H : Point d →L[ℝ] Point d} (hH : ‖H‖ ≤ B) :
    ‖shiftedHessian B H‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  rw [shiftedHessian_apply, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (2 * B)⁻¹)]
  have hv : ‖H v‖ ≤ B * ‖v‖ := (H.le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hH (norm_nonneg _))
  have hn : ‖B • v - H v‖ ≤ 2 * B * ‖v‖ := by
    calc
      _ ≤ ‖B • v‖ + ‖H v‖ := norm_sub_le _ _
      _ ≤ B * ‖v‖ + B * ‖v‖ := by
        rw [norm_smul, Real.norm_of_nonneg hB.le]
        exact add_le_add_left hv _
      _ = _ := by ring
  calc
    _ ≤ (2 * B)⁻¹ * (2 * B * ‖v‖) := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = 1 * ‖v‖ := by field_simp

/-- A spectral upper certificate for the shifted operator is exactly the
lower Hessian Rayleigh certificate needed by the optimization algorithm. -/
theorem shiftedHessian_certificate_iff {d : ℕ} {B : ℝ} (hB : 0 < B)
    (H : Point d →L[ℝ] Point d) (γ : ℝ) :
    (∀ v, ⟪shiftedHessian B H v, v⟫_ℝ ≤ ((B + γ) / (2 * B)) * ‖v‖^2) ↔
      (∀ v, -γ * ‖v‖^2 ≤ ⟪H v, v⟫_ℝ) := by
  have hp : 0 < 2 * B := by positivity
  simp only [shiftedHessian_rayleigh, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hp]
  constructor <;> intro h v <;> have hv := h v <;> nlinarith

/-- A sufficiently large shifted Rayleigh quotient gives a negative
Hessian direction, with the exact threshold conversion. -/
theorem shiftedHessian_negative_iff {d : ℕ} {B : ℝ} (hB : 0 < B)
    (H : Point d →L[ℝ] Point d) (θ : ℝ) {v : Point d} (hv : ‖v‖ = 1) :
    (B + θ) / (2 * B) ≤ ⟪shiftedHessian B H v, v⟫_ℝ ↔ ⟪H v, v⟫_ℝ ≤ -θ := by
  rw [shiftedHessian_rayleigh, hv]
  simp only [one_pow, mul_one, div_le_div_iff_of_pos_right (by positivity : 0 < 2 * B)]
  constructor <;> intro h <;> linarith

end
end SecondOrder
