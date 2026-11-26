import GradientHessian.Model
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Floor.Ring

/-! Integer rounding used in the final optimization.  The selected sizes are
literal manuscript sizes, with no relaxation of the integer parameters. -/

noncomputable section
namespace GradientHessian.ParameterOptimization

def size (J : ℕ) : ℝ := 1 + 4096 * (J : ℝ) ^ 2

theorem size_ge_one (J : ℕ) : 1 ≤ size J := by
  unfold size
  nlinarith [sq_nonneg (J : ℝ)]

theorem size_mono : Monotone size := by
  intro i j hij
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  unfold size
  nlinarith [show (0 : ℝ) ≤ i from Nat.cast_nonneg i,
    show (0 : ℝ) ≤ j from Nat.cast_nonneg j]

theorem size_successor_le {J : ℕ} (hJ : 1 ≤ J) : size (J + 1) ≤ 4 * size J := by
  have hj : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  unfold size
  push_cast
  nlinarith [sq_nonneg ((J : ℝ) - 1)]

/-- The largest admissible size below `x` exists, and loses at most a factor four. -/
theorem size_rounding (J₀ : ℕ) (hJ₀ : 0 < J₀) {x : ℝ} (hx : size J₀ ≤ x) :
    ∃ J : ℕ, J₀ ≤ J ∧ x / 4 ≤ size J ∧ size J ≤ x ∧ x < size (J + 1) := by
  have hex : ∃ j : ℕ, x < size j := by
    obtain ⟨j, hj⟩ := exists_nat_gt x
    refine ⟨j + 1, ?_⟩
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    unfold size
    push_cast
    nlinarith
  let k := Nat.find hex
  have hk : x < size k := Nat.find_spec hex
  have hJk : J₀ < k := by
    by_contra h
    have := size_mono (show k ≤ J₀ by omega)
    linarith
  have hk0 : 0 < k := lt_of_le_of_lt (Nat.zero_le J₀) hJk
  have hkp : k - 1 + 1 = k := by omega
  have hprev : size (k - 1) ≤ x := by
    exact le_of_not_gt (Nat.find_min hex (show k - 1 < k by omega))
  refine ⟨k - 1, by omega, ?_, hprev, ?_⟩
  · have hratio := size_successor_le (J := k - 1) (by omega)
    rw [hkp] at hratio
    linarith
  · simpa only [hkp] using hk

/-- The largest power of eight below a real budget. -/
theorem power_rounding {x : ℝ} (hx : 8 ≤ x) :
    ∃ L : ℕ, 1 ≤ L ∧ x / 8 < (8 : ℝ) ^ L ∧ (8 : ℝ) ^ L ≤ x := by
  let B := ⌊x⌋₊
  have hB : 8 ≤ B := Nat.le_floor hx
  have hB0 : B ≠ 0 := by omega
  refine ⟨Nat.log 8 B, Nat.log_pos (by norm_num) hB, ?_, ?_⟩
  · have hn := Nat.lt_pow_succ_log_self (by norm_num : 1 < 8) B
    have hn' : (B : ℝ) + 1 ≤ (8 : ℝ) ^ (Nat.log 8 B + 1) := by
      exact_mod_cast hn
    have hfloor : x < (B : ℝ) + 1 := Nat.lt_floor_add_one x
    rw [pow_succ] at hn'
    linarith
  · have hn : (8 : ℝ) ^ Nat.log 8 B ≤ (B : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 8 hB0
    exact hn.trans (Nat.floor_le (by linarith))

end GradientHessian.ParameterOptimization
