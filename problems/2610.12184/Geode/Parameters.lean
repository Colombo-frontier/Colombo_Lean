import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Scalar parameter estimates used in the explicit uniform constant.
These do not assert the existence of a hyperbolic resisting oracle. -/
namespace Geode
noncomputable section

def curvatureFactor (R : ℝ) : ℝ := R / Real.tanh R
def cutLatitude (ε : ℝ) : ℝ := 8 * ε / (1 - 16 * ε ^ 2)
def cutContraction (ε : ℝ) : ℝ := Real.sqrt (1 - cutLatitude ε ^ 2)
def radiusBudget (R : ℝ) : ℝ := Real.log (2 * Real.cosh (R / 2))

theorem latitude_bounds {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 64) :
    0 < cutLatitude ε ∧ cutLatitude ε ^ 2 ≤ 65 * ε ^ 2 ∧
      cutLatitude ε ^ 2 < 1 / 2 := by
  have he2 : ε ^ 2 ≤ (1 / 64 : ℝ) ^ 2 := by nlinarith
  have hd : 0 < 1 - 16 * ε ^ 2 := by nlinarith
  have hd' : (255 / 256 : ℝ) ≤ 1 - 16 * ε ^ 2 := by nlinarith
  have hd2 : (255 / 256 : ℝ)^2 ≤ (1 - 16 * ε ^ 2)^2 := by nlinarith
  have hbound : cutLatitude ε ^ 2 ≤ 65 * ε ^ 2 := by
    unfold cutLatitude
    rw [div_pow, div_le_iff₀ (sq_pos_of_pos hd)]
    nlinarith [mul_nonneg (sq_nonneg ε) (show 0 ≤ 65 * (1 - 16 * ε ^ 2)^2 - 64 by nlinarith)]
  refine ⟨div_pos (by linarith) hd, hbound, ?_⟩
  nlinarith

theorem neg_log_sqrt_le {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1 / 2) :
    -Real.log (Real.sqrt (1 - u)) ≤ u := by
  have hd : 0 < 1 - u := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hd
  have hi : (1 - u)⁻¹ - 1 ≤ 2 * u := by
    rw [inv_eq_one_div, sub_le_iff_le_add, div_le_iff₀ hd]
    nlinarith
  rw [Real.log_sqrt (le_of_lt hd)]
  linarith

theorem cut_cost_bounds {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 64) :
    0 < -Real.log (cutContraction ε) ∧
      -Real.log (cutContraction ε) ≤ 65 * ε ^ 2 := by
  obtain ⟨hp, hb, hh⟩ := latitude_bounds he he'
  have hs : 0 < 1 - cutLatitude ε ^ 2 := by linarith
  have hc : 0 < cutContraction ε := Real.sqrt_pos.2 hs
  have hc' : cutContraction ε < 1 := by
    unfold cutContraction
    exact (Real.sqrt_lt' (by norm_num : (0:ℝ) < 1)).2 (by nlinarith)
  constructor
  · exact neg_pos.mpr (Real.log_neg hc hc')
  · exact (neg_log_sqrt_le (sq_nonneg _) (le_of_lt hh)).trans hb

theorem radiusBudget_ge_quarter (R : ℝ) : (R + 1) / 4 ≤ radiusBudget R := by
  have hc : 1 ≤ Real.cosh (R / 2) := Real.one_le_cosh _
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at this ⊢
    exact this
  have h1 : Real.log 2 ≤ radiusBudget R :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have hexp : Real.exp (R / 2) ≤ 2 * Real.cosh (R / 2) := by
    rw [Real.cosh_eq]
    nlinarith [Real.exp_pos (-(R / 2))]
  have h2 : R / 2 ≤ radiusBudget R := by
    have := Real.log_le_log (Real.exp_pos (R / 2)) hexp
    simpa [Real.log_exp, radiusBudget] using this
  linarith

theorem curvatureFactor_le_radius_add_one {R : ℝ} (hR : 0 < R) :
    curvatureFactor R ≤ R + 1 := by
  have hs : 0 < Real.sinh R := Real.sinh_pos_iff.mpr hR
  have he := Real.add_one_le_exp (2 * R)
  have hpos := Real.exp_pos R
  have hprod : Real.exp R * Real.exp R = Real.exp (2 * R) := by
    rw [← Real.exp_add]; congr 1; ring
  have hmul : R ≤ Real.sinh R * Real.exp R := by
    have hid : Real.sinh R * Real.exp R = (Real.exp (2 * R) - 1) / 2 := by
      rw [Real.sinh_eq, Real.exp_neg, ← hprod]
      field_simp
      ring
    rw [hid]
    linarith
  have hsmall : R * Real.exp (-R) ≤ Real.sinh R := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]
    exact hmul
  unfold curvatureFactor
  rw [Real.tanh_eq_sinh_div_cosh, div_div_eq_mul_div, div_le_iff₀ hs]
  nlinarith [Real.cosh_sub_sinh R]

theorem uniform_scalar_budget {R ε : ℝ} (hR : 0 < R)
    (he : 0 < ε) (he' : ε ≤ 1 / 64) :
    curvatureFactor R / (260 * ε ^ 2) ≤
      radiusBudget R / (-Real.log (cutContraction ε)) := by
  obtain ⟨hcost, hcost'⟩ := cut_cost_bounds he he'
  have hz : 0 < curvatureFactor R := by
    unfold curvatureFactor
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos hR (div_pos (Real.sinh_pos_iff.mpr hR) (Real.cosh_pos _))
  have hbudget : curvatureFactor R / 4 ≤ radiusBudget R :=
    (by linarith [curvatureFactor_le_radius_add_one hR] :
      curvatureFactor R / 4 ≤ (R + 1) / 4) |>.trans (radiusBudget_ge_quarter R)
  apply (div_le_div_iff₀ (by positivity : 0 < 260 * ε ^ 2) hcost).2
  nlinarith [mul_nonneg (le_of_lt hz) (sub_nonneg.mpr hcost'),
    mul_nonneg (sq_nonneg ε) (show 0 ≤ 4 * radiusBudget R - curvatureFactor R by linarith)]

def queryHorizon (R ε : ℝ) : ℕ :=
  ⌊radiusBudget R / (-Real.log (cutContraction ε))⌋₊

theorem uniform_horizon_bound {R ε : ℝ} (hR : 0 < R)
    (he : 0 < ε) (he' : ε ≤ 1 / 64) :
    curvatureFactor R / (260 * ε ^ 2) < (queryHorizon R ε : ℝ) + 1 := by
  exact (uniform_scalar_budget hR he he').trans_lt (Nat.lt_floor_add_one _)

theorem radiusBudget_identity {R : ℝ} (hR : 0 < R) :
    radiusBudget R = Real.log (Real.sinh R) - Real.log (Real.sinh (R / 2)) := by
  have hs : 0 < Real.sinh (R / 2) := Real.sinh_pos_iff.mpr (by linarith)
  have hc : 0 < 2 * Real.cosh (R / 2) := by positivity
  have hid : Real.sinh R = 2 * Real.cosh (R / 2) * Real.sinh (R / 2) := by
    have h := Real.sinh_two_mul (R / 2)
    rw [show 2 * (R / 2) = R by ring] at h
    nlinarith
  rw [hid, Real.log_mul (ne_of_gt hc) (ne_of_gt hs)]
  unfold radiusBudget
  ring

/-- Radius survival is conditional on the exact update; the geometry producing
that update is a separate proof obligation. -/
theorem residual_radius_ge_half {R ε S : ℝ} {k : ℕ} (hR : 0 < R)
    (he : 0 < ε) (he' : ε ≤ 1 / 64) (hk : k ≤ queryHorizon R ε)
    (hupdate : Real.sinh S = cutContraction ε ^ k * Real.sinh R) : R / 2 ≤ S := by
  obtain ⟨hcost, _⟩ := cut_cost_bounds he he'
  obtain ⟨_, _, hlat⟩ := latitude_bounds he he'
  have hc : 0 < cutContraction ε := Real.sqrt_pos.2 (by linarith)
  have hsR : 0 < Real.sinh R := Real.sinh_pos_iff.mpr hR
  have hs : 0 < Real.sinh S := by rw [hupdate]; positivity
  have hb : 0 ≤ radiusBudget R := by linarith [radiusBudget_ge_quarter R]
  have hf : (queryHorizon R ε : ℝ) ≤ radiusBudget R / (-Real.log (cutContraction ε)) :=
    Nat.floor_le (div_nonneg hb hcost.le)
  have hk' : (k : ℝ) ≤ radiusBudget R / (-Real.log (cutContraction ε)) :=
    (Nat.cast_le.mpr hk).trans hf
  have hspent := (le_div_iff₀ hcost).mp hk'
  have hlog : Real.log (Real.sinh S) =
      (k : ℝ) * Real.log (cutContraction ε) + Real.log (Real.sinh R) := by
    rw [hupdate, Real.log_mul (ne_of_gt (pow_pos hc k)) (ne_of_gt hsR), Real.log_pow]
  rw [radiusBudget_identity hR] at hspent
  apply Real.sinh_le_sinh.mp
  apply (Real.log_le_log_iff (Real.sinh_pos_iff.mpr (by linarith : 0 < R / 2)) hs).mp
  linarith

theorem tanh_mono {x y : ℝ} (h : x ≤ y) : Real.tanh x ≤ Real.tanh y := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    div_le_div_iff₀ (Real.cosh_pos x) (Real.cosh_pos y)]
  have hs : 0 ≤ Real.sinh (y - x) := Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr h)
  rw [Real.sinh_sub] at hs
  nlinarith

theorem curvatureFactor_three_le {R : ℝ} (hR : 0 < R) :
    curvatureFactor (3 * R) ≤ 3 * curvatureFactor R := by
  have ht : 0 < Real.tanh R := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hR) (Real.cosh_pos _)
  have hm := tanh_mono (show R ≤ 3 * R by linarith)
  have ht3 : 0 < Real.tanh (3 * R) := ht.trans_le hm
  unfold curvatureFactor
  rw [← mul_div_assoc, div_le_div_iff₀ ht3 ht]
  exact mul_le_mul_of_nonneg_left hm (by linarith)

theorem strict_localization_factor {R : ℝ} (hR : 0 < R) :
    3 / 4 * curvatureFactor R ≤ curvatureFactor (3 * R / 4) := by
  have hr : 0 < 3 * R / 4 := by linarith
  have ht : 0 < Real.tanh R := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hR) (Real.cosh_pos _)
  have ht0 : 0 < Real.tanh (3 * R / 4) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hr) (Real.cosh_pos _)
  have hm := tanh_mono (show 3 * R / 4 ≤ R by linarith)
  unfold curvatureFactor
  rw [← mul_div_assoc, div_le_div_iff₀ ht ht0]
  nlinarith [mul_le_mul_of_nonneg_left hm hr.le]

end
end Geode
