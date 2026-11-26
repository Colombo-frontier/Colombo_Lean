import NCBall.ClassParameters
import NCBall.Scaling

/-! # Concrete integer charges and their product complexity scale -/

noncomputable section
namespace NCBall

def calibratedCharges (n : ℕ) (γ L : ℝ) : ℕ := ⌊(n : ℝ) * (L / γ) ^ 2 / 16⌋₊

theorem calibratedCharges_cap (n : ℕ) (γ L : ℝ) :
    (calibratedCharges n γ L : ℝ) ≤ n * (L / γ) ^ 2 / 16 :=
  Nat.floor_le (by positivity)

theorem charge_scale_ge_two {n : ℕ} (hn : 0 < n) {γ L : ℝ} (hγ : 0 < γ)
    (hscale : γ * (bumpConstant + 2) ≤ L / 4) :
    2 ≤ (n : ℝ) * (L / γ) ^ 2 / 16 := by
  have hc := mul_le_mul_of_nonneg_left bumpConstant_ge_one hγ.le
  have hL : 12 * γ ≤ L := by nlinarith
  have hratio : 12 ≤ L / γ := (le_div_iff₀ hγ).mpr hL
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp := mul_le_mul_of_nonneg_right hn' (sq_nonneg (L / γ))
  nlinarith

theorem calibratedCharges_pos {n : ℕ} (hn : 0 < n) {γ L : ℝ} (hγ : 0 < γ)
    (hscale : γ * (bumpConstant + 2) ≤ L / 4) : 0 < calibratedCharges n γ L := by
  have hh : 2 ≤ calibratedCharges n γ L := Nat.le_floor (charge_scale_ge_two hn hγ hscale)
  omega

theorem calibrated_product_lower {n : ℕ} (hn : 0 < n) {γ H Δ L : ℝ}
    (hγ : 0 < γ) (_hH : 0 < H) (_hΔ : 0 ≤ Δ)
    (hregime : 200 * bumpConstant * γ ^ 2 ≤ H * Δ)
    (hscale : γ * (bumpConstant + 2) ≤ L / 4) :
    (n : ℝ) * L ^ 2 * H * Δ / (6400 * bumpConstant * γ ^ 4) ≤
      (calibratedDepth γ H Δ * calibratedCharges n γ L : ℕ) := by
  have hC := bumpConstant_pos
  have hx : 2 ≤ H * Δ / (100 * bumpConstant * γ ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 100 * bumpConstant * γ ^ 2)).mpr
    nlinarith
  have hp := floor_product_lower hx (charge_scale_ge_two hn hγ hscale)
  change _ ≤ ((calibratedDepth γ H Δ * calibratedCharges n γ L : ℕ) : ℝ) at hp
  convert hp using 1
  field_simp
  ring

theorem calibrated_smooth_complexity_lower {n : ℕ} (hn : 0 < n) {η H Δ L : ℝ}
    (hη : 0 < η) (hH : 0 < H) (hΔ : 0 ≤ Δ)
    (hregime : 200 * bumpConstant * (4 * η) ^ 2 ≤ H * Δ)
    (hscale : (4 * η) * (bumpConstant + 2) ≤ L / 4) :
    ((n : ℝ) + 1) * L ^ 2 * H * Δ / (3276800 * bumpConstant * η ^ 4) ≤
      (calibratedDepth (4 * η) H Δ * calibratedCharges n (4 * η) L : ℕ) := by
  have hC := bumpConstant_pos
  have hd := transverse_dimension_half hn
  have hp := calibrated_product_lower hn (by positivity : 0 < 4 * η) hH hΔ hregime hscale
  have hm := mul_le_mul_of_nonneg_right hd
    (by positivity : 0 ≤ L ^ 2 * H * Δ / (6400 * bumpConstant * (4 * η) ^ 4))
  push_cast at hm
  calc
    _ = (((n : ℝ) + 1) / 2) * (L ^ 2 * H * Δ / (6400 * bumpConstant * (4 * η) ^ 4)) := by ring
    _ ≤ (n : ℝ) * (L ^ 2 * H * Δ / (6400 * bumpConstant * (4 * η) ^ 4)) := hm
    _ = (n : ℝ) * L ^ 2 * H * Δ / (6400 * bumpConstant * (4 * η) ^ 4) := by ring
    _ ≤ _ := hp

end NCBall
