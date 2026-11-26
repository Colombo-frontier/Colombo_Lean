import MatchingBounds1005.TensorMasks
import MatchingBounds1005.Confinement

/-! Pointwise analytic confinement with the source's actual polynomial masks. -/
noncomputable section
open scoped InnerProductSpace ContDiff

namespace MatchingBounds1005.TensorGeometry

theorem mask_zero {d : ℕ} (T₃ : Tensor d 3) (T₄ : Tensor d 4) : mask T₃ T₄ 0 = 0 := by
  have h3 := polynomial_value_bound T₃ (0 : Vec d)
  have h4 := polynomial_value_bound T₄ (0 : Vec d)
  norm_num at h3 h4
  simp only [mask, h3, h4, mul_zero, add_zero]

theorem confined_mask_smooth {d : ℕ} {F : Vec d → ℝ} (hF : ContDiff ℝ ∞ F)
    (T₃ : Tensor d 3) (T₄ : Tensor d 4) (R η : ℝ) :
    ContDiff ℝ ∞ (Confinement.objective (fun y => F y + mask T₃ T₄ y) R η) :=
  ((hF.add (mask_smooth T₃ T₄)).comp (radial_contDiff R ∞)).add
    (contDiff_const.mul (contDiff_norm_sq ℝ))

theorem confined_mask_gap {d : ℕ} (F : Vec d → ℝ)
    (T₃ : Tensor d 3) (T₄ : Tensor d 4) {R η Δ δ₃ δ₄ : ℝ}
    (hR : 0 < R) (hη : 0 ≤ η) (hgap : ∀ y, F 0 - F y ≤ Δ)
    (h3 : ‖tensorForm T₃‖ ≤ δ₃) (h4 : ‖tensorForm T₄‖ ≤ δ₄) (x : Vec d) :
    Confinement.objective (fun y => F y + mask T₃ T₄ y) R η 0 -
      Confinement.objective (fun y => F y + mask T₃ T₄ y) R η x ≤
      Δ + δ₃ * R ^ 3 / 3 + δ₄ * R ^ 4 / 4 := by
  have hp := mask_value_bound T₃ T₄ h3 h4 hR.le (radial R x) (radial_norm_lt hR x).le
  have hf := hgap (radial R x)
  have hq : 0 ≤ (η / 2) * ‖x‖ ^ 2 := by positivity
  have hz : radial R (0 : Vec d) = 0 := by simp [radial]
  simp only [Confinement.objective, hz, mask_zero, norm_zero, zero_pow (by omega : 2 ≠ 0),
    mul_zero, add_zero]
  linarith [neg_abs_le (mask T₃ T₄ (radial R x))]

/-- The source's ε-dependent coefficients give exactly the ν = ε/4 budget. -/
theorem source_mask_budgets {ε : ℝ} (hε : 0 < ε) :
    (ε ^ 3 / 8) * (ε⁻¹) ^ 2 + (ε ^ 4 / 8) * (ε⁻¹) ^ 3 = ε / 4 ∧
    (ε ^ 3 / 8) * (ε⁻¹) ^ 3 / 3 + (ε ^ 4 / 8) * (ε⁻¹) ^ 4 / 4 ≤ 1 / 12 ∧
    ε⁻¹ * ((ε ^ 3 / 8) * (ε⁻¹) ^ 2 + (ε ^ 4 / 8) * (ε⁻¹) ^ 3) = 1 / 4 := by
  have he : ε ≠ 0 := hε.ne'
  constructor
  · field_simp
    <;> ring
  constructor
  · have h3 : (ε ^ 3 / 8) * (ε⁻¹) ^ 3 / 3 = 1 / 24 := by field_simp; ring
    have h4 : (ε ^ 4 / 8) * (ε⁻¹) ^ 4 / 4 = 1 / 32 := by field_simp; ring
    rw [h3, h4]
    norm_num
  · field_simp
    <;> ring

theorem source_confined_gap {d : ℕ} (F : Vec d → ℝ)
    (T₃ : Tensor d 3) (T₄ : Tensor d 4) {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ y, F 0 - F y ≤ 1 / 4)
    (h3 : ‖tensorForm T₃‖ ≤ ε ^ 3 / 8) (h4 : ‖tensorForm T₄‖ ≤ ε ^ 4 / 8)
    (x : Vec d) :
    Confinement.objective (fun y => F y + mask T₃ T₄ y) ε⁻¹ (4 * ε ^ 2) 0 -
      Confinement.objective (fun y => F y + mask T₃ T₄ y) ε⁻¹ (4 * ε ^ 2) x ≤ 1 / 3 := by
  have h := confined_mask_gap F T₃ T₄ (inv_pos.mpr hε) (by positivity)
    hgap h3 h4 (η := 4 * ε ^ 2) x
  have hb := (source_mask_budgets hε).2.1
  linarith

/-- Every finite query location is covered, with the source normalized readout
threshold 16ε/b and actual tensor coefficients. -/
theorem source_confined_stationarity {d : ℕ} (F : Vec d → ℝ)
    (T₃ : Tensor d 3) (T₄ : Tensor d 4) (a x : Vec d) {b ε : ℝ}
    (hF : Differentiable ℝ F) (hε : 0 < ε) (ha : ‖a‖ = 1) (hb : 0 < b)
    (hlip : ∀ u v, ‖gradient F u - gradient F v‖ ≤ b * ‖u - v‖)
    (hcert : ∀ z, ⟪a, z⟫_ℝ = 0 → 32 * ε ≤ ‖gradient F z‖)
    (hpair : ∀ y, -(81 / 256 : ℝ) ≤ ⟪y, gradient F y⟫_ℝ)
    (h3 : ‖tensorForm T₃‖ ≤ ε ^ 3 / 8) (h4 : ‖tensorForm T₄‖ ≤ ε ^ 4 / 8)
    (hread : |⟪a, radial ε⁻¹ x⟫_ℝ| ≤ 16 * ε / b) :
    ε < ‖gradient (Confinement.objective (fun y => F y + mask T₃ T₄ y)
      ε⁻¹ (4 * ε ^ 2)) x‖ := by
  have hP : Differentiable ℝ (mask T₃ T₄) := (mask_smooth T₃ T₄).differentiable (by norm_num)
  have hnoise : ∀ y, ‖y‖ ≤ ε⁻¹ → ‖gradient (mask T₃ T₄) y‖ ≤ ε / 4 := by
    intro y hy
    simpa only [(source_mask_budgets hε).1] using
      mask_gradient_bound T₃ T₄ h3 h4 (inv_nonneg.mpr hε.le) y hy
  have htotal : ∀ y, ‖y‖ ≤ ε⁻¹ → -(145 / 256 : ℝ) ≤
      ⟪y, gradient (fun z => F z + mask T₃ T₄ z) y⟫_ℝ := by
    intro y hy
    rw [Confinement.gradient_add_at (hF y) (hP y), inner_add_right]
    have hp := mask_radial_pairing_bound T₃ T₄ h3 h4 (inv_nonneg.mpr hε.le) y hy
    rw [(source_mask_budgets hε).2.2] at hp
    have hf := hpair y
    linarith [neg_abs_le ⟪y, gradient (mask T₃ T₄) y⟫_ℝ]
  have he : 4 * ε / ε⁻¹ = 4 * ε ^ 2 := by simp only [div_inv_eq_mul]; ring
  rw [← he]
  exact Confinement.confined_stationarity F (mask T₃ T₄) a x ε⁻¹ b ε hF hP
    (inv_pos.mpr hε) hε (by simp [hε.ne']) ha hb hlip hcert hnoise htotal hread

end MatchingBounds1005.TensorGeometry
