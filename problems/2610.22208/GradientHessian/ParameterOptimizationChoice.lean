import GradientHessian.ParameterOptimizationRounding
import GradientHessian.ParameterOptimizationArithmetic

/-! Simultaneously admissible integer parameters for the exact parameter theorem. -/

noncomputable section
namespace GradientHessian.ParameterOptimization

structure Choice (E Cd ζ T : ℝ) (d H J₀ : ℕ) where
  J : ℕ
  L : ℕ
  index : J₀ ≤ J
  height : 1 ≤ L
  gap : E * (8 : ℝ) ^ L * size J ≤ T
  dimension : Cd * ((size J) ^ (3 / 2 : ℝ) + Real.log (2 + (8 : ℝ) ^ L)) ≤ d
  rich : (H : ℝ) ≤ (8 : ℝ) ^ L / 2
  rate : (Real.sqrt ζ / (16 * E)) * Model.lowerRate H d T ≤
    (8 : ℝ) ^ L * (size J) ^ (3 / 2 : ℝ)

theorem choice_exists (J₀ : ℕ) (hJ₀ : 0 < J₀) {E Cd ζ T : ℝ} (d H : ℕ)
    (hE : 1 ≤ E) (hCd : 0 ≤ Cd) (hζ : 0 < ζ) (hT : 0 < T)
    (hζE : ζ * E ≤ 1 / 64) (hζd : Cd * ζ ^ (3 / 2 : ℝ) ≤ 1 / 4)
    (hstart : size J₀ ≤ ζ * min ((d : ℝ) ^ (2 / 3 : ℝ)) (T / ((H : ℝ) + 1)))
    (hlog : 4 * Cd * Real.log (2 + T) ≤ d) :
    Nonempty (Choice E Cd ζ T d H J₀) := by
  obtain ⟨J, hJ, hMl, hMu, _⟩ := size_rounding J₀ hJ₀ hstart
  let M := size J
  have hM1 : 1 ≤ M := size_ge_one J
  have hM : 0 < M := by linarith
  have hEp : 0 < E := by linarith
  have hHp : 0 < (H : ℝ) + 1 := by positivity
  have hEM : 1 ≤ E * M := one_le_mul_of_one_le_of_one_le hE hM1
  have hMt : M ≤ ζ * (T / ((H : ℝ) + 1)) :=
    hMu.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hζ.le)
  have hMt' : M * ((H : ℝ) + 1) ≤ ζ * T := by
    apply (le_div_iff₀ hHp).mp
    simpa only [mul_div_assoc] using hMt
  have hx : 64 * ((H : ℝ) + 1) ≤ T / (E * M) := by
    apply (le_div_iff₀ (mul_pos hEp hM)).mpr
    have h1 := mul_le_mul_of_nonneg_left hMt' hEp.le
    have h2 := mul_le_mul_of_nonneg_right hζE hT.le
    nlinarith only [h1, h2]
  obtain ⟨L, hL, hnl, hnu⟩ := power_rounding (show 8 ≤ T / (E * M) by
    have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
    linarith)
  let n : ℝ := 8 ^ L
  have hn0 : 0 ≤ n := by dsimp [n]; positivity
  have hgap : E * n * M ≤ T := by
    have := (le_div_iff₀ (mul_pos hEp hM)).mp hnu
    dsimp [n]
    nlinarith only [this]
  have hnT : n ≤ T := by
    have := mul_le_mul_of_nonneg_left hEM hn0
    nlinarith only [this, hgap]
  have hrich : (H : ℝ) ≤ n / 2 := by
    have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
    dsimp [n]
    linarith
  have hMd : M ≤ ζ * (d : ℝ) ^ (2 / 3 : ℝ) :=
    hMu.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hζ.le)
  have hpower := dimension_power_bound hM.le hζ.le (Nat.cast_nonneg d) hMd
  have hdim1 : Cd * M ^ (3 / 2 : ℝ) ≤ (d : ℝ) / 4 := by
    have h1 := mul_le_mul_of_nonneg_left hpower hCd
    have h2 := mul_le_mul_of_nonneg_right hζd (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
    nlinarith only [h1, h2]
  have hdim2 : Cd * Real.log (2 + n) ≤ (d : ℝ) / 4 := by
    have hl := Real.log_le_log (show 0 < 2 + n by linarith) (by linarith : 2 + n ≤ 2 + T)
    have := mul_le_mul_of_nonneg_left hl hCd
    linarith
  have hdimension : Cd * (M ^ (3 / 2 : ℝ) + Real.log (2 + n)) ≤ d := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith only [hdim1, hdim2, hd0]
  have hnround : T / (8 * E * M) ≤ n := by
    have he : T / (8 * E * M) = T / (E * M) / 8 := by ring
    rw [he]
    exact hnl.le
  exact ⟨⟨J, L, hJ, hL, hgap, hdimension, hrich,
    rounded_rate_bound H d hEp hζ.le hM hT.le hMl hnround⟩⟩

end GradientHessian.ParameterOptimization
