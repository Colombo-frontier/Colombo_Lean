import LowerMain
import SphereSmoothingSharpParameters
import AdaptiveSpherePosteriorSecondMoment

open MeasureTheory

namespace Task006.Full

open Task006.UpperPublicParameters

theorem minimax_two_sided {d : ℕ} {L R eps : ℝ} (h : Regime d L R eps) :
    (d : ℝ)*(L*R/eps)^3/131072 ≤ (minimaxReplies.{0,0} d L R eps : ℝ) ∧
    (minimaxReplies.{0,0} d L R eps : ℝ) ≤
      (2*publicComplexityCoefficient)*d*(L*R/eps)^3*
        Real.log (Real.exp 1*d*(L*R/eps))^(3/2:ℝ) :=
  ⟨minimax_lower_complexity h,minimax_upper_complexity h⟩

/-- An absolute constant, chosen before all problem parameters and instances,
gives the complete upper and lower minimax statement of the manuscript. -/
theorem main_theorem : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (L R eps : ℝ), Regime d L R eps →
    (d : ℝ)*(L*R/eps)^3/131072 ≤ (minimaxReplies.{0,0} d L R eps : ℝ) ∧
    (minimaxReplies.{0,0} d L R eps : ℝ) ≤ C*d*(L*R/eps)^3*
      Real.log (Real.exp 1*d*(L*R/eps))^(3/2:ℝ) := by
  refine ⟨2*publicComplexityCoefficient,?_,fun d L R eps h => minimax_two_sided h⟩
  have hp := publicLogCoefficient_pos
  unfold publicComplexityCoefficient
  positivity

/-- The polynomial logarithmic envelope in the closing corollary. -/
theorem logarithm_product_le_twice_sum (d A : ℝ) (hd : 0 < d) (hA : 0 < A) :
    Real.log (Real.exp 1*d*A) ≤ 2*Real.log (Real.exp 1+d+A) := by
  have he : Real.exp 1 ≤ 4 := Real.exp_one_lt_three.le.trans (by norm_num)
  have h1 : Real.exp 1*d*A ≤ 4*d*A :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hd.le) hA.le
  have h2 : 4*d*A ≤ (d+A)^2 := by nlinarith [sq_nonneg (d-A)]
  have h3 : (d+A)^2 ≤ (Real.exp 1+d+A)^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith [Real.exp_pos 1]) 2
  have hl := Real.log_le_log (by positivity : 0 < Real.exp 1*d*A) ((h1.trans h2).trans h3)
  simpa only [Real.log_pow,Nat.cast_ofNat] using hl

#print axioms main_theorem
#print axioms minimax_two_sided
#print axioms logarithm_product_le_twice_sum

end Task006.Full
