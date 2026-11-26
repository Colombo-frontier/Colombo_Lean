import FreshGradientMinimax.LevelEstimator
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-! The explicit logarithmic step count in F.1 and equation (45), for the
actual level kernel. `RelativeEstimator` and `EstimatorCost` use this level
accuracy to analyse the independent multilevel mixture and its work tags. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

theorem geometric_decay_log_ceiling {t R : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hR : 0 < R) :
    (1 - t) ^ ⌈Real.log R / t⌉₊ ≤ 1 / R := by
  have hceil := Nat.le_ceil (Real.log R / t)
  have hlog := (div_le_iff₀ ht).mp hceil
  have hbase : 1 - t ≤ Real.exp (-t) := by
    simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-t)
  have hp := pow_le_pow_left₀ (sub_nonneg.mpr ht1) hbase ⌈Real.log R / t⌉₊
  rw [← Real.exp_nat_mul] at hp
  calc
    _ ≤ _ := hp
    _ ≤ Real.exp (-Real.log R) := Real.exp_le_exp.mpr (by nlinarith only [hlog])
    _ = _ := by rw [Real.exp_neg, Real.exp_log hR, one_div]

def levelSteps (ℓ α γ m : ℝ) (b : ℕ) : ℕ :=
  ⌈(ℓ / α) * Real.log (4 * (b : ℝ) * (1 + ℓ ^ 2 / (γ * m ^ 2)))⌉₊

theorem levelSteps_contraction {ℓ α γ m : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α) (hαℓ : α ≤ ℓ)
    (hγ : 0 < γ) (hm : 0 < m) {b : ℕ} (hb : 0 < b) :
    ℓ ^ 2 * (1 - α / ℓ) ^ levelSteps ℓ α γ m b ≤ γ * m ^ 2 / b := by
  let R := 4 * (b : ℝ) * (1 + ℓ ^ 2 / (γ * m ^ 2))
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hR : 0 < R := by dsimp [R]; positivity
  have ht := geometric_decay_log_ceiling (div_pos hα hℓ) ((div_le_one hℓ).mpr hαℓ) hR
  have he : Real.log R / (α / ℓ) = (ℓ / α) * Real.log R := by field_simp; ring
  rw [he] at ht
  change (1 - α / ℓ) ^ levelSteps ℓ α γ m b ≤ 1 / R at ht
  have ht' := mul_le_mul_of_nonneg_left ht (sq_nonneg ℓ)
  have hcoef : ℓ ^ 2 / R ≤ γ * m ^ 2 / b := by
    apply (div_le_div_iff₀ hR hbR).mpr
    have heq : γ * m ^ 2 * R = 4 * (b : ℝ) * (γ * m ^ 2 + ℓ ^ 2) := by
      dsimp [R]
      field_simp
    rw [heq]
    nlinarith [mul_nonneg (sq_nonneg ℓ) hbR.le,
      mul_nonneg (mul_nonneg hγ.le (sq_nonneg m)) hbR.le]
  calc
    _ ≤ ℓ ^ 2 * (1 / R) := ht'
    _ = ℓ ^ 2 / R := by ring
    _ ≤ _ := hcoef

namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem selected_level_accuracy (K : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {γ m : ℝ} (hγ : 0 < γ) (hm : 0 < m)
    {b : ℕ} (hb : 0 < b) (v a : Euclid dy) (u : Euclid dx) :
    (∫ r, ‖r - (gradient S.effectiveValue v + a)‖ ^ 2
      ∂S.levelKernel K b (levelSteps ℓ α γ m b) v a u) ≤
        (γ * m ^ 2 * ‖u - S.sliceMin v‖ ^ 2 + 10 * σ ^ 2) / b := by
  have hlev := S.levelKernel_error K hb hαℓ (levelSteps ℓ α γ m b) v a u
  have hc := levelSteps_contraction S.toNCObjective.L_pos S.α_pos hαℓ hγ hm hb
  have hc' := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖u - S.sliceMin v‖)
  have hratio : ℓ / α ≤ 4 := (div_le_iff₀ S.α_pos).mpr (by linarith)
  have hnoise : (ℓ / α + 1) * σ ^ 2 / b ≤ 10 * σ ^ 2 / b := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg σ)
  calc
    _ ≤ (γ * m ^ 2 / b) * ‖u - S.sliceMin v‖ ^ 2 + 10 * σ ^ 2 / b := by linarith
    _ = _ := by ring

/-- Equation (45), with each H_j an actual finite fresh-sampling kernel. -/
theorem dyadic_level_accuracy (K : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {γ m : ℝ} (hγ : 0 < γ) (hm : 0 < m)
    (j : ℕ) (v a : Euclid dy) (u : Euclid dx) :
    (∫ r, ‖r - (gradient S.effectiveValue v + a)‖ ^ 2
      ∂S.levelKernel K (2 ^ j) (levelSteps ℓ α γ m (2 ^ j)) v a u) ≤
        (1 / 2 : ℝ) ^ j * (γ * m ^ 2 * ‖u - S.sliceMin v‖ ^ 2 + 10 * σ ^ 2) := by
  have h := S.selected_level_accuracy K hαℓ hfast hγ hm (pow_pos (by norm_num : 0 < (2 : ℕ)) j) v a u
  have he : (1 / 2 : ℝ) ^ j = ((2 : ℝ) ^ j)⁻¹ := by rw [one_div, inv_pow]
  rw [he]
  simpa only [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, mul_comm] using h

theorem dyadic_level_bias (K : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {γ m : ℝ} (hγ : 0 < γ) (hm : 0 < m)
    (j : ℕ) (v a : Euclid dy) (u : Euclid dx) :
    ‖(∫ r, r ∂S.levelKernel K (2 ^ j) (levelSteps ℓ α γ m (2 ^ j)) v a u) -
        (gradient S.effectiveValue v + a)‖ ^ 2 ≤
      (1 / 2 : ℝ) ^ j * (γ * m ^ 2 * ‖u - S.sliceMin v‖ ^ 2 + 10 * σ ^ 2) := by
  have hb : 0 < (2 : ℕ) ^ j := pow_pos (by norm_num) j
  exact (squared_bias_le_second_moment (fun r => r) (gradient S.effectiveValue v + a)
    (S.levelKernel_integrable K hb _ v a u) (S.levelKernel_square_integrable K hb _ v a u)).trans
    (S.dyadic_level_accuracy K hαℓ hfast hγ hm j v a u)

end SCObjective
end FreshGradientMinimax
