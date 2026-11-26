import Smoothness2601.DeferredDimension
import Smoothness2601.ChainWrapper

/-! The explicit deferred-prefix ambient dimension has the manuscript's
epsilon^-2 log(1/epsilon) rate when the call budget is polynomial in 1/epsilon. -/
noncomputable section
namespace Smoothness2601.DeferredPrefix

theorem logarithm_polynomial_budget {M T : ℕ} (hM : 1 ≤ M) (hT : 1 ≤ T)
    {u CM CT : ℝ} (hu : 1 ≤ u) (hlu : 1 ≤ Real.log u)
    (hCM : 1 ≤ CM) (hCT : 1 ≤ CT)
    (hMb : (M : ℝ) ≤ CM*u^6) (hTb : (T : ℝ) ≤ CT*u^2) :
    Real.log (16*(M : ℝ)*T) ≤ (Real.log (16*CM*CT)+8)*Real.log u := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hM0 : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hT0 : (0:ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hC0 : 0 < 16*CM*CT := by positivity
  have hprod : 16*(M : ℝ)*T ≤ (16*CM*CT)*u^8 := by
    have hh := mul_le_mul hMb hTb hT0.le (by positivity : 0 ≤ CM*u^6)
    calc
      _ ≤ 16*((CM*u^6)*(CT*u^2)) := by nlinarith only [hh]
      _ = _ := by ring
  have hlog := Real.log_le_log (by positivity : 0 < 16*(M : ℝ)*T) hprod
  rw [Real.log_mul hC0.ne' (pow_pos hu0 8).ne',Real.log_pow] at hlog
  have hC1 : 1 ≤ 16*CM*CT := by nlinarith
  have hlC := Real.log_nonneg hC1
  have hh := mul_le_mul_of_nonneg_left hlu hlC
  norm_num at hlog
  nlinarith

theorem ambientDimension_polynomial_rate (M T : ℕ) (hM : 1 ≤ M) (hT : 1 ≤ T)
    {δ R u CM CT CR : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hu : 1 ≤ u) (hlu : 1 ≤ Real.log u) (hCM : 1 ≤ CM) (hCT : 1 ≤ CT)
    (hCR : 0 ≤ CR) (hMb : (M : ℝ) ≤ CM*u^6) (hTb : (T : ℝ) ≤ CT*u^2)
    (hRadius : R^2 ≤ CR*T) :
    (ambientDimension M T δ R : ℝ) ≤
      (CT+2+(8*CR*CT/δ^2)*(Real.log (16*CM*CT)+8))*u^2*Real.log u := by
  have hdim := (ambientDimension_upper M T hM hT hδ hR).le
  have hlog := logarithm_polynomial_budget hM hT hu hlu hCM hCT hMb hTb
  have hu2 : 1 ≤ u^2 := by nlinarith
  have hlu0 : 0 ≤ Real.log u := by linarith
  have hlog0 : 0 ≤ Real.log (16*(M : ℝ)*T) := by
    apply Real.log_nonneg
    have hm : (1:ℝ) ≤ M := by exact_mod_cast hM
    have ht : (1:ℝ) ≤ T := by exact_mod_cast hT
    nlinarith
  have hrad : 8*R^2/δ^2 ≤ (8*CR*CT/δ^2)*u^2 := by
    have hb := hRadius.trans (mul_le_mul_of_nonneg_left hTb hCR)
    have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 8)) (sq_nonneg δ)
    exact hh.trans_eq (by ring)
  have hterm := mul_le_mul hrad hlog hlog0 (by positivity : 0 ≤ (8*CR*CT/δ^2)*u^2)
  have hu2log : u^2 ≤ u^2*Real.log u := by nlinarith
  have hbase : (T : ℝ)+2 ≤ (CT+2)*u^2*Real.log u := by
    have hmain := mul_le_mul_of_nonneg_left hu2log (by linarith : 0 ≤ CT)
    nlinarith
  calc
    _ ≤ (T : ℝ)+2+(8*R^2/δ^2)*Real.log (16*(M : ℝ)*T) := hdim
    _ ≤ (CT+2)*u^2*Real.log u+
        ((8*CR*CT/δ^2)*u^2)*((Real.log (16*CM*CT)+8)*Real.log u) := add_le_add hbase hterm
    _ = _ := by ring

theorem chainRadius_sq (CH : ℝ) (n : ℕ) :
    ExtensiveChain.chainRadius CH n ^ 2 = (4096*CH^2)*(n+1) := by
  unfold ExtensiveChain.chainRadius
  have he : Real.sqrt ((n : ℝ)+1)^2 = (n : ℝ)+1 := Real.sq_sqrt (by positivity)
  nlinarith only [he]

end Smoothness2601.DeferredPrefix
