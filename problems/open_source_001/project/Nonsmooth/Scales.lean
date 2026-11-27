import Nonsmooth.Basic

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem radius_nonneg {g μ R : ℝ} (hg : 0 ≤ g) (hμ : 0 < μ) (hR : 0 ≤ R) :
    0 ≤ radius g μ R := le_min hR (div_nonneg hg hμ.le)

theorem radius_le_R (g μ R : ℝ) : radius g μ R ≤ R := min_le_left _ _

theorem mul_radius_le {g μ R : ℝ} (hμ : 0 < μ) : μ * radius g μ R ≤ g := by
  have := (le_div_iff₀ hμ).mp (min_le_right R (g / μ))
  simpa [radius, mul_comm] using this

theorem radius_eq_interior {g μ R : ℝ} (hμ : 0 < μ) (hg : g ≤ μ * R) :
    radius g μ R = g / μ := by
  exact min_eq_right ((div_le_iff₀ hμ).mpr (by nlinarith))

theorem radius_eq_boundary {g μ R : ℝ} (hμ : 0 < μ) (hg : μ * R ≤ g) :
    radius g μ R = R := by
  exact min_eq_left ((le_div_iff₀ hμ).mpr (by nlinarith))

theorem energy_interior {g μ R : ℝ} (hμ : 0 < μ) (hg : g ≤ μ * R) :
    energy g μ R = g ^ 2 / (2 * μ) := by
  rw [energy, radius_eq_interior hμ hg]
  field_simp
  <;> ring

theorem energy_boundary {g μ R : ℝ} (hμ : 0 < μ) (hg : μ * R ≤ g) :
    energy g μ R = g * R - μ / 2 * R ^ 2 := by
  rw [energy, radius_eq_boundary hμ hg]

theorem radial_maximizer {g μ R r : ℝ} (hg : 0 ≤ g) (hμ : 0 < μ)
    (hR : 0 ≤ R) (hr0 : 0 ≤ r) (hrR : r ≤ R) :
    g * r - μ / 2 * r ^ 2 ≤ energy g μ R := by
  rcases le_total g (μ * R) with h | h
  · rw [energy_interior hμ h, le_div_iff₀ (by positivity : 0 < 2 * μ)]
    nlinarith [sq_nonneg (g - μ * r)]
  · rw [energy_boundary hμ h]
    have hp : 0 ≤ (R - r) * (g - μ * R) := mul_nonneg (by linarith) (by linarith)
    have hq := mul_nonneg hμ.le (sq_nonneg (R - r))
    nlinarith

theorem energy_nonneg {g μ R : ℝ} (hg : 0 ≤ g) (hμ : 0 < μ) (hR : 0 ≤ R) :
    0 ≤ energy g μ R := by
  simpa using radial_maximizer hg hμ hR (le_refl 0) hR

theorem energy_pos {g μ R : ℝ} (hg : 0 < g) (hμ : 0 < μ) (hR : 0 < R) :
    0 < energy g μ R := by
  have hr : 0 < radius g μ R := lt_min hR (div_pos hg hμ)
  have hm := mul_radius_le (g := g) (R := R) hμ
  have hp := mul_le_mul_of_nonneg_right hm hr.le
  have hgr := mul_pos hg hr
  unfold energy
  nlinarith

theorem energy_le_quadratic {g μ R : ℝ} (hμ : 0 < μ) :
    energy g μ R ≤ g ^ 2 / (2 * μ) := by
  rw [energy, le_div_iff₀ (by positivity : 0 < 2 * μ)]
  nlinarith [sq_nonneg (g - μ * radius g μ R)]

theorem energy_le_gR {g μ R : ℝ} (hg : 0 ≤ g) (hμ : 0 < μ) :
    energy g μ R ≤ g * R := by
  have := mul_le_mul_of_nonneg_left (radius_le_R g μ R) hg
  have := mul_nonneg hμ.le (sq_nonneg (radius g μ R))
  unfold energy
  nlinarith

theorem localModulus_le_two_gap {g μ R : ℝ} (hμ : 0 < μ) :
    localModulus g μ R ≤ 2 * g := by
  have := mul_radius_le (g := g) (R := R) hμ
  unfold localModulus
  linarith

theorem scale_comparison {g μ R : ℝ} (hg : 0 ≤ g) (hμ : 0 < μ) (hR : 0 ≤ R) :
    scaleH (g + μ * R) g μ R / 4 ≤ energy g μ R ∧
      energy g μ R ≤ scaleH (g + μ * R) g μ R := by
  have hH1 := min_le_left ((g + μ * R) * R) (g ^ 2 / μ)
  have hH2 := min_le_right ((g + μ * R) * R) (g ^ 2 / μ)
  have hsq : 0 ≤ g ^ 2 / μ := div_nonneg (sq_nonneg _) hμ.le
  constructor
  · rcases le_total g (μ * R) with h | h
    · rw [energy_interior hμ h]
      have he : g ^ 2 / (2 * μ) = (g ^ 2 / μ) / 2 := by ring
      rw [he]
      unfold scaleH
      linarith
    · rw [energy_boundary hμ h]
      have hp := mul_le_mul_of_nonneg_right h hR
      unfold scaleH
      nlinarith
  · apply le_min
    · have := energy_le_gR (R := R) hg hμ
      nlinarith [mul_nonneg hμ.le (sq_nonneg R)]
    · have := energy_le_quadratic (g := g) (R := R) hμ
      have he : g ^ 2 / (2 * μ) = (g ^ 2 / μ) / 2 := by ring
      rw [he] at this
      linarith

theorem energy_le_local_product {g μ R : ℝ} (hμ : 0 < μ) :
    energy g μ R ≤ localModulus g μ R * radius g μ R := by
  unfold energy localModulus
  nlinarith [mul_nonneg hμ.le (sq_nonneg (radius g μ R))]

theorem local_product_le_two_H {g μ R : ℝ} (hg : 0 ≤ g) (hμ : 0 < μ)
    (hR : 0 ≤ R) :
    localModulus g μ R * radius g μ R ≤ 2 * scaleH (g + μ * R) g μ R := by
  unfold scaleH
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  apply le_min
  · have hr := radius_le_R g μ R
    have hr0 := radius_nonneg hg hμ hR
    have hmod : localModulus g μ R ≤ g + μ * R := by
      unfold localModulus
      nlinarith
    have hmod0 : 0 ≤ localModulus g μ R := by unfold localModulus; positivity
    have hp := mul_le_mul hmod hr hr0 (by positivity : 0 ≤ g + μ * R)
    nlinarith [mul_nonneg (show 0 ≤ g + μ * R by positivity) hR]
  · have hm := localModulus_le_two_gap (g := g) (R := R) hμ
    have hr := (min_le_right R (g / μ))
    have hp := mul_le_mul hm hr (radius_nonneg hg hμ hR) (by positivity : 0 ≤ 2 * g)
    change localModulus g μ R * radius g μ R ≤ 2 * (g ^ 2 / μ)
    calc
      localModulus g μ R * radius g μ R = localModulus g μ R * min R (g / μ) := rfl
      _ ≤ 2 * g * (g / μ) := hp
      _ = 2 * (g ^ 2 / μ) := by ring

end
end Nonsmooth
