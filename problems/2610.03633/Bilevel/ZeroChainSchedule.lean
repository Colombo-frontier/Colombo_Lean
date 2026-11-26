import Bilevel.ZeroChainMultiscale
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! The exact numerical multiscale schedule specified in the manuscript. -/

noncomputable section
namespace Bilevel.ZeroChainSchedule

def levels (θ : ℝ) : ℕ := Nat.floor (Real.logb 4 (max 1 (Real.log θ)))
def aExponent (j : ℕ) : ℝ := 1-1/(4:ℝ)^(j+1)
def bExponent (j : ℕ) : ℝ := 1-1/(2*(4:ℝ)^j)
def resolution (c β θ : ℝ) (j : ℕ) : ℝ := c*β*θ^(-aExponent j)
def width (c β θ : ℝ) (j : ℕ) : ℝ := c*β*θ^(-bExponent j)

theorem levels_power_bounds (θ : ℝ) :
    (4:ℝ)^(levels θ) ≤ max 1 (Real.log θ) ∧ max 1 (Real.log θ) < (4:ℝ)^(levels θ+1) := by
  have ht : (0:ℝ) < max 1 (Real.log θ) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hn : 0 ≤ Real.logb 4 (max 1 (Real.log θ)) := Real.logb_nonneg (by norm_num) (le_max_left _ _)
  have hlo : (levels θ:ℝ) ≤ Real.logb 4 (max 1 (Real.log θ)) := Nat.floor_le hn
  have hhi : Real.logb 4 (max 1 (Real.log θ)) < (levels θ:ℝ)+1 := Nat.lt_floor_add_one _
  constructor
  · simpa only [Real.rpow_natCast] using (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ) < 4) ht).mp hlo
  · have hh := (Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ) < 4) ht).mp hhi
    simpa only [Real.rpow_add (by norm_num : (0:ℝ) < 4), Real.rpow_natCast, Real.rpow_one, pow_succ] using hh

theorem log_ge_four_of_levels_pos (θ : ℝ) (hJ : 0 < levels θ) : 4 ≤ Real.log θ := by
  have hp : (4:ℝ) ≤ 4^(levels θ) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) hJ
  have hm := hp.trans (levels_power_bounds θ).1
  rcases le_max_iff.mp hm with h | h
  · norm_num at h
  · exact h

theorem four_power_le_log (θ : ℝ) (j : ℕ) (hj : j < levels θ) : (4:ℝ)^(j+1) ≤ Real.log θ := by
  have hlog := log_ge_four_of_levels_pos θ (by omega)
  have hl := (levels_power_bounds θ).1
  rw [max_eq_right (by linarith : 1 ≤ Real.log θ)] at hl
  exact (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) (show j+1 ≤ levels θ by omega)).trans hl

theorem aExponent_nonneg (j : ℕ) : 0 ≤ aExponent j := by
  have hp : (1:ℝ) ≤ 4^(j+1) := one_le_pow₀ (by norm_num)
  have hd : 1/(4:ℝ)^(j+1) ≤ 1 := (div_le_one (by positivity)).mpr hp
  dsimp [aExponent]
  linarith

theorem bExponent_nonneg (j : ℕ) : 0 ≤ bExponent j := by
  have hp : (1:ℝ) ≤ 4^j := one_le_pow₀ (by norm_num)
  have hd : 1/(2*(4:ℝ)^j) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  dsimp [bExponent]
  linarith

theorem resolution_pos (c β θ : ℝ) (hc : 0 < c) (hβ : 0 < β) (hθ : 1 ≤ θ) (j : ℕ) :
    0 < resolution c β θ j := by
  dsimp [resolution]
  exact mul_pos (mul_pos hc hβ) (Real.rpow_pos_of_pos (by linarith) _)

theorem width_pos (c β θ : ℝ) (hc : 0 < c) (hβ : 0 < β) (hθ : 1 ≤ θ) (j : ℕ) :
    0 < width c β θ j := by
  dsimp [width]
  exact mul_pos (mul_pos hc hβ) (Real.rpow_pos_of_pos (by linarith) _)

theorem resolution_le_amplitude (c β θ : ℝ) (hc : 0 ≤ c) (hβ : 0 ≤ β) (hθ : 1 ≤ θ) (j : ℕ) :
    resolution c β θ j ≤ c*β := by
  apply mul_le_of_le_one_right (mul_nonneg hc hβ)
  exact Real.rpow_le_one_of_one_le_of_nonpos hθ (neg_nonpos.mpr (aExponent_nonneg j))

theorem resolution_small (c β θ : ℝ) (hc : 0 ≤ c) (hcsmall : c ≤ 1/16)
    (hβ : 0 ≤ β) (hθ : 1 ≤ θ) (j : ℕ) : resolution c β θ j ≤ β/16 := by
  exact (resolution_le_amplitude c β θ hc hβ hθ j).trans (by nlinarith [mul_le_mul_of_nonneg_right hcsmall hβ])

/-- Any two distinct interior resolutions are separated by at least a factor
two; the paper's schedule actually supplies the stronger factor exp(3). -/
theorem resolutions_separated (c β θ : ℝ) (hc : 0 ≤ c) (hβ : 0 ≤ β) (hθ : 1 ≤ θ)
    (i j : ℕ) (hij : i < j) (hj : j < levels θ) :
    2*resolution c β θ j ≤ resolution c β θ i := by
  have hθpos : 0 < θ := by linarith
  have hlog : 0 ≤ Real.log θ := Real.log_nonneg hθ
  have hP : 0 < (4:ℝ)^(j+1) := by positivity
  have hQ : 0 < (4:ℝ)^(i+1) := by positivity
  have hPQ : 4*(4:ℝ)^(i+1) ≤ (4:ℝ)^(j+1) := by
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) (show (i+1)+1 ≤ j+1 by omega)
    simpa only [pow_succ, mul_comm] using hh
  have hdiv : 4/(4:ℝ)^(j+1) ≤ 1/(4:ℝ)^(i+1) := (div_le_div_iff₀ hP hQ).mpr (by nlinarith)
  have hmul := mul_le_mul_of_nonneg_right hdiv hlog
  have hrat : 1 ≤ Real.log θ/(4:ℝ)^(j+1) := (one_le_div hP).mpr (four_power_le_log θ j hj)
  have he : Real.log θ*(-aExponent j)+3 ≤ Real.log θ*(-aExponent i) := by
    dsimp [aExponent]
    simp only [div_eq_mul_inv] at hmul hrat ⊢
    nlinarith
  have hexp := Real.exp_le_exp.mpr he
  rw [Real.exp_add] at hexp
  have he3 : 2 ≤ Real.exp 3 := by nlinarith [Real.add_one_le_exp 3]
  have hp := mul_le_mul_of_nonneg_left he3 (Real.exp_pos (Real.log θ*(-aExponent j))).le
  have hh : 2*Real.exp (Real.log θ*(-aExponent j)) ≤ Real.exp (Real.log θ*(-aExponent i)) := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hh (mul_nonneg hc hβ)
  dsimp [resolution]
  rw [Real.rpow_def_of_pos hθpos, Real.rpow_def_of_pos hθpos]
  nlinarith

theorem width_formula (c β θ : ℝ) (hθ : 1 ≤ θ) (j : ℕ) :
    width c β θ j = (c*β/θ)*Real.exp (Real.log θ/(2*(4:ℝ)^j)) := by
  have hθpos : 0 < θ := by linarith
  rw [width, Real.rpow_def_of_pos hθpos]
  have he : Real.log θ*(-bExponent j) = -Real.log θ+Real.log θ/(2*(4:ℝ)^j) := by
    dsimp [bExponent]
    ring
  rw [he, Real.exp_add, Real.exp_neg, Real.exp_log hθpos]
  ring

theorem final_width_bounds (c β θ : ℝ) (hc : 0 ≤ c) (hβ : 0 ≤ β) (hθ : 1 ≤ θ) :
    c*β/θ ≤ width c β θ (levels θ) ∧
      width c β θ (levels θ) ≤ Real.exp 2*c*β/θ := by
  have hθpos : 0 < θ := by linarith
  have hp : 0 < (4:ℝ)^(levels θ) := by positivity
  have hlog : 0 ≤ Real.log θ := Real.log_nonneg hθ
  have hupper : Real.log θ < 4*(4:ℝ)^(levels θ) := by
    have hh := (le_max_right 1 (Real.log θ)).trans_lt (levels_power_bounds θ).2
    simpa only [pow_succ, mul_comm] using hh
  have hr0 : 0 ≤ Real.log θ/(2*(4:ℝ)^(levels θ)) := by positivity
  have hr2 : Real.log θ/(2*(4:ℝ)^(levels θ)) ≤ 2 :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have he0 : 1 ≤ Real.exp (Real.log θ/(2*(4:ℝ)^(levels θ))) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hr0
  have he2 := Real.exp_le_exp.mpr hr2
  rw [width_formula c β θ hθ]
  constructor
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left he0 (by positivity : 0 ≤ c*β/θ)
  · exact (mul_le_mul_of_nonneg_left he2 (by positivity : 0 ≤ c*β/θ)).trans_eq (by ring)

theorem width_antitone (c β θ : ℝ) (hc : 0 ≤ c) (hβ : 0 ≤ β) (hθ : 1 ≤ θ)
    (i j : ℕ) (hij : i ≤ j) : width c β θ j ≤ width c β θ i := by
  have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) hij
  have hd : 1/(2*(4:ℝ)^j) ≤ 1/(2*(4:ℝ)^i) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hc hβ)
  apply Real.rpow_le_rpow_of_exponent_le hθ
  dsimp [bExponent]
  linarith

theorem exponent_balance (j : ℕ) : 2*aExponent j-bExponent j = 1 ∧
    2*bExponent (j+1)-aExponent j = 1 := by
  dsimp [aExponent,bExponent]
  constructor
  · rw [pow_succ]
    field_simp
    ring
  · ring

theorem source_at_most_three_active_pieces (n : ℕ) (c θ : ℝ) (hc : 0 < c)
    (hcsmall : c ≤ 1/16) (hθ : 1 ≤ θ) (z : ZeroChain.Space n) :
    (ZeroChainMultiscale.activePieces n (levels θ) (resolution c 1 θ) z).card ≤ 3 := by
  apply ZeroChainMultiscale.at_most_three_active_pieces
  · intro j _
    exact resolution_pos c 1 θ hc (by norm_num) hθ j
  · intro j _
    simpa using resolution_small c 1 θ hc.le hcsmall (by norm_num) hθ j
  · intro i j hij hj
    exact resolutions_separated c 1 θ hc.le (by norm_num) hθ i j hij hj

end Bilevel.ZeroChainSchedule
