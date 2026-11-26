import HeavyTail.OnlineMasterTuning
import HeavyTail.GaussianStageMoments
import HeavyTail.LocalizationSchedule

/-! Reduction of the genuine accepted-law scales to the manuscript's fixed
threshold amplitude. The constant depends on p alone. -/
noncomputable section
namespace HeavyTail

def acceptedStageConstant (p : ℝ) : ℝ :=
  (96 + 16 * GaussianEstimates.mixedConstant p) *
    (8 + Real.sqrt (rejectionConstant p) + 2 * rejectionConstant p +
      (rejectionConstant p) ^ (1 / p)) + 8 * rejectionConstant p + 2

theorem acceptedStageConstant_pos (p : ℝ) : 0 < acceptedStageConstant p := by
  unfold acceptedStageConstant
  have hC := rejectionConstant_pos p
  have hD := GaussianEstimates.mixedConstant_pos p
  positivity

theorem accepted_rate_scalar {D C p G W B s R ell n : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hG : 0 ≤ G) (hW : 0 ≤ W)
    (hB : 0 ≤ B) (hs : 0 ≤ s) (hR : 0 ≤ R) (hell : 1 ≤ ell) (hn : ell ≤ n) :
    D * R * ((4 * G + C * B + Real.sqrt (C * W)) / Real.sqrt n +
      (4 * G + C * B) * ell / n + C ^ (1 / p) * s * (ell / n) ^ (1 - 1 / p)) +
      8 * R * (C * B) + 2 * G * R / n ≤
    (D * (8 + Real.sqrt C + 2 * C + C ^ (1 / p)) + 8 * C + 2) * R *
      ((G + Real.sqrt W) / Real.sqrt n + G * ell / n +
        s * (ell / n) ^ (1 - 1 / p) + B) := by
  have hn1 : 1 ≤ n := hell.trans hn
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn1
  have hsn : 1 ≤ Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn1
  have he0 : 0 ≤ ell := le_trans zero_le_one hell
  have hrpow : 0 ≤ C ^ (1 / p) := Real.rpow_nonneg hC _
  let A := (G + Real.sqrt W) / Real.sqrt n
  let H := s * (ell / n) ^ (1 - 1 / p)
  let J := G * ell / n
  let F := A + J + H + B
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hAF : A ≤ F := by dsimp [F]; linarith
  have hJF : J ≤ F := by dsimp [F]; linarith
  have hHF : H ≤ F := by dsimp [F]; linarith
  have hBF : B ≤ F := by dsimp [F]; linarith
  have hGr : G / Real.sqrt n ≤ A := by
    exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (Real.sqrt_nonneg W))
      (Real.sqrt_nonneg n)
  have hWr : Real.sqrt W / Real.sqrt n ≤ A := by
    exact div_le_div_of_nonneg_right (le_add_of_nonneg_left hG) (Real.sqrt_nonneg n)
  have hBr : C * B / Real.sqrt n ≤ C * B := by
    apply (div_le_iff₀ (Real.sqrt_pos.2 hn0)).2
    nlinarith [mul_nonneg hC hB]
  have hBe : C * B * ell / n ≤ C * B := by
    apply (div_le_iff₀ hn0).2
    exact mul_le_mul_of_nonneg_left hn (mul_nonneg hC hB)
  have hroot : (4 * G + C * B + Real.sqrt (C * W)) / Real.sqrt n ≤
      (4 + Real.sqrt C) * A + C * B := by
    rw [Real.sqrt_mul hC]
    have h0 := mul_le_mul_of_nonneg_left hGr (by norm_num : (0 : ℝ) ≤ 4)
    have h1 := mul_le_mul_of_nonneg_left hWr (Real.sqrt_nonneg C)
    calc
      _ = 4 * (G / Real.sqrt n) + C * B / Real.sqrt n +
          Real.sqrt C * (Real.sqrt W / Real.sqrt n) := by ring
      _ ≤ 4 * A + C * B + Real.sqrt C * A := by linarith
      _ = _ := by ring
  have hdet : (4 * G + C * B) * ell / n ≤ 4 * J + C * B := by
    dsimp [J]
    calc
      _ = 4 * (G * ell / n) + C * B * ell / n := by ring
      _ ≤ _ := add_le_add_left hBe _
  have hsum : (4 * G + C * B + Real.sqrt (C * W)) / Real.sqrt n +
      (4 * G + C * B) * ell / n + C ^ (1 / p) * s * (ell / n) ^ (1 - 1 / p) ≤
      (8 + Real.sqrt C + 2 * C + C ^ (1 / p)) * F := by
    have h0 := mul_le_mul_of_nonneg_left hAF
      (by positivity : 0 ≤ 4 + Real.sqrt C)
    have h1 := mul_le_mul_of_nonneg_left hJF (by norm_num : (0 : ℝ) ≤ 4)
    have h2 := mul_le_mul_of_nonneg_left hHF hrpow
    have h3 := mul_le_mul_of_nonneg_left hBF hC
    have heq : C ^ (1 / p) * s * (ell / n) ^ (1 - 1 / p) = C ^ (1 / p) * H := by
      dsimp [H]; ring
    rw [heq]
    calc
      _ ≤ ((4 + Real.sqrt C) * A + C * B) + (4 * J + C * B) + C ^ (1 / p) * H :=
        add_le_add_right (add_le_add hroot hdet) _
      _ ≤ ((4 + Real.sqrt C) * F + C * F) + (4 * F + C * F) + C ^ (1 / p) * F :=
        add_le_add (add_le_add (add_le_add h0 h3) (add_le_add h1 h3)) h2
      _ = _ := by ring
  have hmain := mul_le_mul_of_nonneg_left hsum (mul_nonneg hD hR)
  have hbias := mul_le_mul_of_nonneg_left hBF (by positivity : 0 ≤ 8 * R * C)
  have hGn : G / n ≤ F := by
    have hsample := online_inverse_sample_rate hG (by norm_num : (0 : ℝ) ≤ 1) hn1
    simp only [mul_one] at hsample
    exact hsample.trans (hGr.trans hAF)
  have hprox := mul_le_mul_of_nonneg_left hGn (by positivity : 0 ≤ 2 * R)
  change _ ≤ (D * (8 + Real.sqrt C + 2 * C + C ^ (1 / p)) + 8 * C + 2) * R * F
  convert add_le_add (add_le_add hmain hbias) hprox using 1 <;> ring

theorem accepted_rate_bound (θ : OracleParameters) {α τ R : ℝ} {n : ℕ}
    (hτ : 64 * (4 * θ.G + θ.L) ≤ τ) (hα : 0 < α) (hα1 : α < 1 / 10)
    (hR : 0 ≤ R) (hn : confidenceLog α ≤ (n : ℝ)) :
    (96 + 16 * GaussianEstimates.mixedConstant θ.p) * R *
      ((acceptedMeanScale θ τ + Real.sqrt (acceptedTraceScale θ τ)) / Real.sqrt n +
        acceptedMeanScale θ τ * confidenceLog α / n +
        acceptedWeakScale θ * (confidenceLog α / n) ^ (1 - 1 / θ.p)) +
      8 * R * acceptedBiasScale θ τ + 2 * θ.G * R / n ≤
    acceptedStageConstant θ.p * R *
      fixedThresholdAmplitude θ.G θ.L θ.s θ.p α τ n := by
  have hL := θ.s_pos.trans_le θ.s_le_L
  have hS := θ.s_pos
  have hD := GaussianEstimates.mixedConstant_pos θ.p
  have ht : 0 < τ := by linarith [θ.G_pos]
  have hW : 0 ≤ θ.L ^ θ.p * τ ^ (2 - θ.p) := by positivity
  have hB : 0 ≤ θ.s * (θ.L / τ) ^ (θ.p - 1) := by positivity
  have h := accepted_rate_scalar (p := θ.p)
    (D := 96 + 16 * GaussianEstimates.mixedConstant θ.p)
    (C := rejectionConstant θ.p) (G := θ.G)
    (W := θ.L ^ θ.p * τ ^ (2 - θ.p))
    (B := θ.s * (θ.L / τ) ^ (θ.p - 1)) (s := θ.s) (R := R)
    (ell := confidenceLog α) (n := (n : ℝ))
    (by positivity) (rejectionConstant_pos θ.p).le θ.G_pos.le hW hB θ.s_pos.le hR
    (confidenceLog_ge_one hα hα1) hn
  simpa only [acceptedStageConstant, acceptedMeanScale, acceptedBiasScale,
    acceptedTraceScale, acceptedWeakScale, fixedThresholdAmplitude, one_div,
    mul_assoc] using h

end HeavyTail
