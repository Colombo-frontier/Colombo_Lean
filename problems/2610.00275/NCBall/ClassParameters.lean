import NCBall.ChainRegularity
import NCBall.ChainGap

/-! # Explicit parameter choices for the deterministic function-class conditions

We choose Cρ = 2 Cχ and cM = 1 / (100 Cχ). The stochastic Lipschitz
second moment is a separate obligation; it is not assumed or claimed here.
-/

noncomputable section
open Set Metric
open scoped NNReal
namespace NCBall

def calibratedRho (γ H : ℝ) : ℝ := 2 * bumpConstant * γ / H
def calibratedLam (γ : ℝ) : ℝ := γ / (16 * bumpConstant)
def calibratedDepth (γ H Δ : ℝ) : ℕ := ⌊H * Δ / (100 * bumpConstant * γ ^ 2)⌋₊

theorem calibratedRho_pos {γ H : ℝ} (hγ : 0 < γ) (hH : 0 < H) :
    0 < calibratedRho γ H := by
  have := bumpConstant_pos
  unfold calibratedRho
  positivity

theorem calibratedLam_bounds {γ : ℝ} (hγ : 0 ≤ γ) :
    0 ≤ calibratedLam γ ∧ calibratedLam γ ≤ γ / 2 := by
  have hC := bumpConstant_ge_one
  have hCp := bumpConstant_pos
  unfold calibratedLam
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : 0 < 16 * bumpConstant)).2
    nlinarith [mul_le_mul_of_nonneg_left hC hγ]

theorem calibratedDepth_ge_two {γ H Δ : ℝ} (hγ : 0 < γ)
    (hregime : 200 * bumpConstant * γ ^ 2 ≤ H * Δ) :
    2 ≤ calibratedDepth γ H Δ := by
  have hC := bumpConstant_pos
  apply Nat.le_floor
  apply (le_div_iff₀ (by positivity : 0 < 100 * bumpConstant * γ ^ 2)).2
  norm_num
  nlinarith

theorem calibrated_smoothness_coefficient {γ H : ℝ} (hγ : 0 < γ) (hH : 0 < H) :
    ((calibratedLam γ * 2 + γ) * bumpConstant / calibratedRho γ H) ≤ H := by
  have hρ := calibratedRho_pos hγ hH
  have hl := (calibratedLam_bounds hγ.le).2
  have hC := bumpConstant_pos
  apply (div_le_iff₀ hρ).2
  have heq : H * calibratedRho γ H = 2 * bumpConstant * γ := by
    unfold calibratedRho
    field_simp
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_right hl hC.le]

theorem calibrated_gradient_lipschitz {n M : ℕ} {γ H : ℝ}
    (hγ : 0 < γ) (hH : 0 < H) (U : ℕ → Space n)
    (hU : ∀ i, U i 0 = 0) (hgood : ∀ i < M, ‖U i‖ ≤ 2) :
    LipschitzWith ⟨H, hH.le⟩
      (gradient (chainValue M (calibratedRho γ H) γ (calibratedLam γ)
        (roomCenter (calibratedRho γ H) U) U)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_mk]
  exact (chainValue_gradient_norm_sub (calibratedRho_pos hγ hH) hγ.le
    (calibratedLam_bounds hγ.le).1 (by norm_num) U U hU hgood x y).trans
    (mul_le_mul_of_nonneg_right (calibrated_smoothness_coefficient hγ hH) (norm_nonneg _))

theorem calibrated_gap_arithmetic {γ H Δ : ℝ}
    (hγ : 0 < γ) (hH : 0 < H) (hΔ : 0 ≤ Δ) :
    40 * calibratedDepth γ H Δ * γ * calibratedRho γ H ≤ Δ := by
  have hC := bumpConstant_pos
  have hf : (calibratedDepth γ H Δ : ℝ) * (100 * bumpConstant * γ ^ 2) ≤ H * Δ := by
    apply (le_div_iff₀ (by positivity : 0 < 100 * bumpConstant * γ ^ 2)).mp
    exact Nat.floor_le (by positivity)
  have heq : 40 * calibratedDepth γ H Δ * γ * calibratedRho γ H =
      (80 * bumpConstant * calibratedDepth γ H Δ * γ ^ 2) / H := by
    unfold calibratedRho
    ring
  rw [heq]
  apply (div_le_iff₀ hH).2
  nlinarith [mul_nonneg hC.le (mul_nonneg (Nat.cast_nonneg (calibratedDepth γ H Δ))
    (sq_nonneg γ))]

theorem calibrated_gap {n : ℕ} {γ H Δ : ℝ}
    (hγ : 0 < γ) (hH : 0 < H) (hΔ : 0 ≤ Δ)
    (hM : 1 ≤ calibratedDepth γ H Δ) (U : ℕ → Space n)
    (hU : ∀ i, U i 0 = 0) (hgood : ∀ i < calibratedDepth γ H Δ, ‖U i‖ ≤ 2) :
    let M := calibratedDepth γ H Δ
    let ρ := calibratedRho γ H
    let f := chainValue M ρ γ (calibratedLam γ) (roomCenter ρ U) U
    f 0 - sInf (f '' closedBall 0 (37 * M * ρ)) ≤ Δ := by
  dsimp only
  have hρ := calibratedRho_pos hγ hH
  have hl := calibratedLam_bounds hγ.le
  have hb := chainValue_gap_infimum hρ hM hγ.le hl.1 (by norm_num : (0 : ℝ) ≤ 2)
    (by positivity : 0 ≤ 37 * calibratedDepth γ H Δ * calibratedRho γ H)
    U U hU hgood
  have hM' : (1 : ℝ) ≤ calibratedDepth γ H Δ := by exact_mod_cast hM
  have ha : γ * (37 * calibratedDepth γ H Δ * calibratedRho γ H) +
      calibratedLam γ * calibratedRho γ H * 2 + γ * calibratedRho γ H ≤
      40 * calibratedDepth γ H Δ * γ * calibratedRho γ H := by
    nlinarith [mul_le_mul_of_nonneg_right hl.2 hρ.le,
      mul_le_mul_of_nonneg_right hM' (mul_nonneg hγ.le hρ.le)]
  exact hb.trans (ha.trans (calibrated_gap_arithmetic hγ hH hΔ))

/-- The analytic conclusions in (7.4)--(7.5), excluding only the stochastic
Lipschitz moment, for the actual family with fixed absolute constants. -/
theorem deterministic_class_verification {n : ℕ} {η H Δ : ℝ}
    (hη : 0 < η) (hH : 0 < H) (hΔ : 0 ≤ Δ)
    (hregime : 200 * bumpConstant * (4 * η) ^ 2 ≤ H * Δ)
    (U : ℕ → Space n) (hU : ∀ i, U i 0 = 0)
    (hgood : ∀ i < calibratedDepth (4 * η) H Δ, ‖U i‖ ≤ 2) :
    let M := calibratedDepth (4 * η) H Δ
    let ρ := calibratedRho (4 * η) H
    let f := chainValue M ρ (4 * η) (calibratedLam (4 * η)) (roomCenter ρ U) U
    LipschitzWith ⟨H, hH.le⟩ (gradient f) ∧
      f 0 - sInf (f '' closedBall 0 (37 * M * ρ)) ≤ Δ ∧
      gradient f (roomCenter ρ U M) = 0 ∧
      (∀ x, ‖gradient f x‖ ≤ η → x ∈ closedBall (roomCenter ρ U M) ρ) ∧
      (∀ j ≤ M, closedBall (roomCenter ρ U j) ρ ⊆ closedBall 0 (37 * M * ρ)) := by
  dsimp only
  have hγ : 0 < 4 * η := by positivity
  have hρ := calibratedRho_pos hγ hH
  have hM := calibratedDepth_ge_two hγ hregime
  refine ⟨calibrated_gradient_lipschitz hγ hH U hU hgood,
    calibrated_gap hγ hH hΔ (by omega) U hU hgood,
    terminal_center_gradient_zero hρ U U hU, ?_, ?_⟩
  · intro x hx
    exact stationary_point_in_terminal_room hρ hη U hU hgood x hx
  · intro j hj x hx
    exact all_rooms_in_query_ball hρ.le (by omega) U hgood hj hx

end NCBall
