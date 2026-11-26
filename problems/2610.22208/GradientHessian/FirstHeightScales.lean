import GradientHessian.InnerSelfDerivatives
import Mathlib.Data.Nat.Log

/-! An explicit source-compatible power-of-two radius choice. The number
of physical registers grows with log M, while derivative constants do not. -/

noncomputable section
namespace GradientHessian.FirstHeight

def baseRadius (M : ℕ) : ℝ := 2 ^ Nat.clog 2 M
def depth (M : ℕ) : ℕ := Nat.clog 2 M + 1
def outerRadius (M : ℕ) : ℝ := Inner.lastRadius (depth M)

theorem outerRadius_eq (M : ℕ) : outerRadius M = 4 * baseRadius M := by
  simp only [outerRadius, Inner.lastRadius, depth, baseRadius, pow_add, pow_one]
  ring

theorem baseRadius_range {M : ℕ} (hM : 1 ≤ M) : (M : ℝ) ≤ baseRadius M ∧ baseRadius M < 2 * M := by
  constructor
  · unfold baseRadius
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) M
  · by_cases h : M = 1
    · subst M; norm_num [baseRadius, Nat.clog]
    · have hm : 1 < M := by omega
      have hc : 0 < Nat.clog 2 M := Nat.clog_pos (by norm_num) hm
      have hp : (2 : ℝ) ^ (Nat.clog 2 M).pred < M := by
        exact_mod_cast Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hm
      have he : Nat.clog 2 M = (Nat.clog 2 M).pred + 1 := (Nat.succ_pred_eq_of_pos hc).symm
      unfold baseRadius
      rw [he, pow_succ]
      linarith

theorem outerRadius_range {M : ℕ} (hM : 1 ≤ M) :
    4 * (M : ℝ) ≤ outerRadius M ∧ outerRadius M < 8 * M := by
  rw [outerRadius_eq]
  have h := baseRadius_range hM
  constructor <;> linarith [h.1, h.2]

theorem register_count_le_radius (k : ℕ) : (k + 2 : ℝ) ≤ Inner.lastRadius k := by
  induction k with
  | zero => norm_num [Inner.lastRadius]
  | succ k ih =>
    simp only [Inner.lastRadius, pow_succ] at ih ⊢
    push_cast
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith

theorem sqrt_register_count_bound {M : ℕ} (hM : 1 ≤ M) :
    Real.sqrt (depth M + 2) ≤ 3 * M := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hc := register_count_le_radius (depth M)
  have hr := (outerRadius_range hM).2
  change Inner.lastRadius (depth M) < 8 * (M : ℝ) at hr
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ depth M + 2 by positivity)
  have hn := Real.sqrt_nonneg (depth M + 2 : ℝ)
  nlinarith [sq_nonneg ((M : ℝ) - 1)]

variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- All eight actual self residuals have the source first-order scale. -/
theorem self_first_derivative_bound {M : ℕ} (hM : 1 ≤ M)
    (v : Fin 8 → Fin (depth M + 2) → E) (hv : ∀ i j, ‖v i j‖ = 1)
    (Z : InnerCoordinates.Space F E 8 (depth M + 2)) :
    ‖iteratedFDeriv ℝ 1 (Inner.sumResidual v) Z‖ ≤ 9 * LatchLemma.latchConstant * (M : ℝ) ^ 2 := by
  have h := Inner.sumResidual_first_derivative_bound v hv Z
  have hc := sqrt_register_count_bound hM
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have h8 : Real.sqrt (8 : ℝ) ≤ 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8), Real.sqrt_nonneg (8 : ℝ)]
  have hprod := mul_le_mul hc h8 (Real.sqrt_nonneg _) (by positivity : (0 : ℝ) ≤ 3 * M)
  have hmul := mul_le_mul_of_nonneg_left hprod LatchLemma.latchConstant_pos.le
  have hp := mul_nonneg LatchLemma.latchConstant_pos.le (show (0 : ℝ) ≤ (M : ℝ)^2 - M by nlinarith)
  norm_num only [Nat.cast_ofNat] at h
  nlinarith

end GradientHessian.FirstHeight
