import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! # An explicit finite ambient dimension for the actual Haar probe bound -/

noncomputable section

namespace NCConcave16991.Haar

def ambientDimension (n U blocks probes : ℕ) (C r : ℝ) : ℕ :=
  n + U + 1 + ⌈6 * (blocks : ℝ) * probes * C ^ 2 / r ^ 2⌉₊

theorem sourceRows_le_ambient (n U blocks probes : ℕ) (C r : ℝ) :
    n ≤ ambientDimension n U blocks probes C r := by
  unfold ambientDimension
  omega

theorem readBudget_lt_ambient (n U blocks probes : ℕ) (C r : ℝ) :
    U < ambientDimension n U blocks probes C r := by
  unfold ambientDimension
  omega

theorem ambient_remainder (n U blocks probes : ℕ) (C r : ℝ) :
    ambientDimension n U blocks probes C r - U =
      n + 1 + ⌈6 * (blocks : ℝ) * probes * C ^ 2 / r ^ 2⌉₊ := by
  unfold ambientDimension
  omega

theorem ambient_probe_bound (n U blocks probes : ℕ) (C r : ℝ) (hr : 0 < r) :
    (blocks : ℝ) * probes * C ^ 2 /
      (((ambientDimension n U blocks probes C r - U : ℕ) : ℝ) * r ^ 2) ≤ 1 / 6 := by
  have hd : 0 < ambientDimension n U blocks probes C r - U :=
    Nat.sub_pos_of_lt (readBudget_lt_ambient n U blocks probes C r)
  have hdR : (0 : ℝ) < (ambientDimension n U blocks probes C r - U : ℕ) := by exact_mod_cast hd
  have hc := Nat.le_ceil (6 * (blocks : ℝ) * probes * C ^ 2 / r ^ 2)
  have hnum := (div_le_iff₀ (sq_pos_of_pos hr)).1 hc
  have hceil : (⌈6 * (blocks : ℝ) * probes * C ^ 2 / r ^ 2⌉₊ : ℝ) ≤
      ((ambientDimension n U blocks probes C r - U : ℕ) : ℝ) := by
    rw [ambient_remainder]
    simp only [Nat.cast_add, Nat.cast_one]
    linarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
  have hm := mul_le_mul_of_nonneg_right hceil (sq_nonneg r)
  apply (div_le_iff₀ (mul_pos hdR (sq_pos_of_pos hr))).2
  nlinarith only [hnum, hm]

end NCConcave16991.Haar
