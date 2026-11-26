import Smoothness2601.GeometricBatches

/-! Explicit uniform constants for the source's inner-solve sample bound. -/
noncomputable section
open scoped BigOperators
namespace Smoothness2601.InnerCost

def constant (q A : ℝ) : ℝ :=
  1 + 5 / (-Real.log q) + 4*A/(1-Real.sqrt q) ^ 2

theorem constant_pos {q A : ℝ} (hq : 0 < q) (hq1 : q < 1) (hA : 0 ≤ A) :
    0 < constant q A := by
  have hl : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq hq1)
  unfold constant
  positivity

theorem iterations_bound {q D u : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hD : 0 ≤ D) (hu : 0 < u) (hu1 : u ≤ 1) :
    (GeometricBatches.iterations q D u : ℝ) ≤
      (1+3/(-Real.log q))*(1/u ^ 2) + (2/(-Real.log q))*Real.log (2+D/u) := by
  have hd : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq hq1)
  have hu2 : 0 < u ^ 2 := sq_pos_of_pos hu
  have hw : 1 ≤ 1/u ^ 2 := (le_div_iff₀ hu2).mpr (by nlinarith)
  have hR : 1 ≤ 4*(D+1) ^ 2/u ^ 2 :=
    (le_div_iff₀ hu2).mpr (by nlinarith [sq_nonneg D])
  have harg : D+1 ≤ 2+D/u := by
    have hDu : D ≤ D/u := (le_div_iff₀ hu).mpr (by nlinarith)
    linarith
  have hlogD := Real.log_le_log (by positivity : 0 < D+1) harg
  have hlog4 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
  have hlogu := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 1/u ^ 2)
  rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (ne_of_gt hu2), Real.log_one,
    Real.log_pow] at hlogu
  norm_num only at hlogu
  have hn : Real.log (4*(D+1) ^ 2/u ^ 2) ≤ 3*(1/u ^ 2)+2*Real.log (2+D/u) := by
    rw [Real.log_div (by positivity) (ne_of_gt hu2),
      Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by positivity), Real.log_pow, Real.log_pow]
    norm_num only
    nlinarith
  have hn0 : 0 ≤ Real.log (4*(D+1) ^ 2/u ^ 2)/(-Real.log q) :=
    div_nonneg (Real.log_nonneg hR) hd.le
  have hceil := Nat.ceil_lt_add_one hn0
  have hmax : (GeometricBatches.iterations q D u : ℝ) ≤
      1+Real.log (4*(D+1) ^ 2/u ^ 2)/(-Real.log q) := by
    unfold GeometricBatches.iterations
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith) (by linarith)
  have hdiv := div_le_div_of_nonneg_right hn hd.le
  calc
    (GeometricBatches.iterations q D u : ℝ) ≤
      1+(3*(1/u ^ 2)+2*Real.log (2+D/u))/(-Real.log q) := by linarith
    _ ≤ (1+3/(-Real.log q))*(1/u ^ 2) + (2/(-Real.log q))*Real.log (2+D/u) := by
      simp only [div_eq_mul_inv] at *
      nlinarith

theorem sample_bound {q A D u : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hu : 0 < u) (hu1 : u ≤ 1) :
    (∑ k ∈ Finset.range (GeometricBatches.iterations q D u),
      (GeometricBatches.batch q A u (GeometricBatches.iterations q D u) k : ℝ)) ≤
        constant q A*(1/u ^ 2+Real.log (2+D/u)) := by
  have hd : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq hq1)
  have hs : Real.sqrt q < 1 := (Real.sqrt_lt' (by norm_num)).mpr (by simpa using hq1)
  have hlog : 0 ≤ Real.log (2+D/u) := Real.log_nonneg (by
    have : 0 ≤ D/u := by positivity
    linarith)
  have ht := GeometricBatches.total_cost (u := u) hq1 hA (GeometricBatches.iterations q D u)
  have hJ := iterations_bound hq hq1 hD hu hu1
  have he : 4*A/(u ^ 2*(1-Real.sqrt q) ^ 2) =
      (4*A/(1-Real.sqrt q) ^ 2)*(1/u ^ 2) := by
        field_simp
        rw [mul_comm (u ^ 2)]
  rw [he] at ht
  have hc0 : 0 ≤ 4*A/(1-Real.sqrt q) ^ 2 := by positivity
  have hdl : 0 ≤ 1/(-Real.log q) := by positivity
  have hw : 0 ≤ 1/u ^ 2 := by positivity
  have h1 := mul_nonneg hdl hw
  have h2 := mul_nonneg hdl hlog
  have h3 := mul_nonneg hc0 hlog
  unfold constant
  simp only [div_eq_mul_inv] at *
  nlinarith

end Smoothness2601.InnerCost
