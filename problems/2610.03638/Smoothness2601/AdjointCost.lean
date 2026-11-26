import Smoothness2601.GeometricBatches

/-! The logarithmic iteration count when the adjoint initialization radius is
a fixed public constant, including the source's fixed accuracy rescaling. -/
noncomputable section
namespace Smoothness2601.AdjointCost

def iterationConstant (q D : ℝ) : ℝ :=
  (1+2*Real.log (D+1)/(-Real.log q))/Real.log 2+2/(-Real.log q)

theorem iterationConstant_pos {q D : ℝ} (hq : 0 < q) (hq1 : q < 1) (hD : 0 ≤ D) :
    0 < iterationConstant q D := by
  have hd : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq hq1)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hDlog : 0 ≤ Real.log (D+1) := Real.log_nonneg (by linarith)
  unfold iterationConstant
  positivity

theorem iterations_log {q D u : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hD : 0 ≤ D) (hu : 0 < u) (hu1 : u ≤ 1) :
    (GeometricBatches.iterations q D u : ℝ) ≤ iterationConstant q D*Real.log (2/u) := by
  have hd : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq hq1)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hDlog : 0 ≤ Real.log (D+1) := Real.log_nonneg (by linarith)
  have hL := Real.log_le_log (by norm_num : (0:ℝ) < 2)
    ((le_div_iff₀ hu).mpr (by nlinarith : (2:ℝ)*u ≤ 2))
  have hR : 1 ≤ 4*(D+1) ^ 2/u ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hu)).mpr (by nlinarith [sq_nonneg D])
  have hn0 : 0 ≤ Real.log (4*(D+1) ^ 2/u ^ 2)/(-Real.log q) :=
    div_nonneg (Real.log_nonneg hR) hd.le
  have hceil := Nat.ceil_lt_add_one hn0
  have hJ : (GeometricBatches.iterations q D u : ℝ) ≤
      1+Real.log (4*(D+1) ^ 2/u ^ 2)/(-Real.log q) := by
    unfold GeometricBatches.iterations
    rw [Nat.cast_max,Nat.cast_one]
    exact max_le (by linarith) (by linarith)
  have he : Real.log (4*(D+1) ^ 2/u ^ 2) = 2*Real.log (2/u)+2*Real.log (D+1) := by
    rw [Real.log_div (by positivity) (by positivity),Real.log_mul (by norm_num : (4:ℝ) ≠ 0)
      (by positivity),Real.log_pow,Real.log_pow,
      Real.log_div (by norm_num : (2:ℝ) ≠ 0) hu.ne']
    have h4 : Real.log 4 = 2*Real.log 2 := by
      calc
        Real.log 4 = Real.log ((2:ℝ) ^ 2) := by norm_num
        _ = 2*Real.log 2 := Real.log_pow (2:ℝ) 2
    rw [h4]
    ring
  rw [he] at hJ
  have hcoef : 0 ≤ (1+2*Real.log (D+1)/(-Real.log q))/Real.log 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hL hcoef
  rw [div_mul_cancel₀ _ hl2.ne'] at hm
  unfold iterationConstant
  simp only [div_eq_mul_inv] at *
  nlinarith

def scaleConstant (c : ℝ) : ℝ := 1+Real.log (max 1 c)/Real.log 2

theorem scaleConstant_pos (c : ℝ) : 0 < scaleConstant c := by
  have hs : 0 ≤ Real.log (max (1:ℝ) c) := Real.log_nonneg (le_max_left _ _)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold scaleConstant
  positivity

theorem log_scale {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Real.log (2/(ε/c)) ≤ scaleConstant c*Real.log (2/ε) := by
  have hs : 0 < max (1:ℝ) c := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL := Real.log_le_log (by norm_num : (0:ℝ) < 2)
    ((le_div_iff₀ hε).mpr (by nlinarith : (2:ℝ)*ε ≤ 2))
  have he : 2/(ε/c) = c*(2/ε) := by field_simp; ring
  have harg : 2/(ε/c) ≤ max 1 c*(2/ε) := by
    rw [he]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hh := Real.log_le_log (by positivity : (0:ℝ) < 2/(ε/c)) harg
  rw [Real.log_mul hs.ne' (by positivity : (2/ε:ℝ) ≠ 0)] at hh
  have hlogs : 0 ≤ Real.log (max (1:ℝ) c) := Real.log_nonneg (le_max_left _ _)
  have hm := mul_le_mul_of_nonneg_left hL (div_nonneg hlogs hl2.le)
  rw [div_mul_cancel₀ _ hl2.ne'] at hm
  unfold scaleConstant
  nlinarith

end Smoothness2601.AdjointCost
