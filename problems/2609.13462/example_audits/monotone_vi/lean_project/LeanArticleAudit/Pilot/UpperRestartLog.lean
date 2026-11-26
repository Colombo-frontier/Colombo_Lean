import LeanArticleAudit.Pilot.UpperCost

/-!
# Logarithmic comparison for the restart transformation

This file isolates the scalar estimate comparing every residual subcall's
logarithmic factor with the public strong-solver logarithm.
-/

namespace LeanArticleAudit.Pilot

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The positive argument occurring inside `strongLog`. -/
def restartStrongArgument (data : VIPublicData E) (mu delta : ℝ) : ℝ :=
  2 + data.Lp * data.D ^ (data.p - 1) / mu +
    data.Lp * data.D ^ data.p / delta + mu * data.D / delta

theorem restartStrongArgument_two_le (data : VIPublicData E) (mu delta : ℝ)
    (hmu : 0 < mu) (hdelta : 0 < delta) :
    2 ≤ restartStrongArgument data mu delta := by
  unfold restartStrongArgument
  have hD : 0 ≤ data.D := data.D_pos.le
  have hLp : 0 ≤ data.Lp := data.Lp_pos.le
  have h₁ : 0 ≤ data.Lp * data.D ^ (data.p - 1) / mu := by positivity
  have h₂ : 0 ≤ data.Lp * data.D ^ data.p / delta := by positivity
  have h₃ : 0 ≤ mu * data.D / delta := by positivity
  linarith

theorem strongLog_eq_restartStrongArgument (data : VIPublicData E)
    (mu delta : ℝ) :
    strongLog data mu delta =
      1 + Real.log (restartStrongArgument data mu delta) := by
  rfl

/-- If a residual subcall's inverse-radius term and condition number are
controlled by the strong logarithm's argument, then its complete logarithmic
factor is at most four strong-log units.  This deliberately includes a large
constant margin, so callers can use the same estimate for ordinary halving
calls and for the final-accuracy call. -/
theorem residualLog_le_four_strongLog_of_bounds
    (data : VIPublicData E) (mu delta R epsilon : ℝ)
    (hmu : 0 < mu) (hdelta : 0 < delta)
    (hR : 0 < R) (hepsilon : 0 < epsilon)
    (hinv : data.D / R ≤ restartStrongArgument data mu delta)
    (hcond : residualCondition data R epsilon ≤
      2 * restartStrongArgument data mu delta) :
    residualLog data R epsilon ≤ 4 * strongLog data mu delta := by
  let S := restartStrongArgument data mu delta
  have hS2 : 2 ≤ S := restartStrongArgument_two_le data mu delta hmu hdelta
  have hSpos : 0 < S := lt_of_lt_of_le (by norm_num) hS2
  have hargpos : 0 < 2 + data.D / R + residualCondition data R epsilon := by
    have hDdiv : 0 ≤ data.D / R := div_nonneg data.D_pos.le hR.le
    have hq : 0 ≤ residualCondition data R epsilon := by
      unfold residualCondition
      exact div_nonneg
        (mul_nonneg data.Lp_pos.le (pow_nonneg hR.le data.p)) hepsilon.le
    linarith
  have hargle : 2 + data.D / R + residualCondition data R epsilon ≤ 4 * S := by
    dsimp [S] at hinv hcond ⊢
    linarith
  have hlogle : Real.log
      (2 + data.D / R + residualCondition data R epsilon) ≤
        Real.log (4 * S) := by
    exact Real.log_le_log hargpos hargle
  have hlogS0 : 0 ≤ Real.log S := Real.log_nonneg (by linarith)
  have hlog4 : Real.log (4 : ℝ) ≤ 3 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4) using 1 <;>
      norm_num
  have hmul : Real.log (4 * S) = Real.log 4 + Real.log S := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hSpos.ne']
  rw [residualLog, strongLog_eq_restartStrongArgument]
  change 1 + Real.log
      (2 + data.D / R + residualCondition data R epsilon) ≤
    4 * (1 + Real.log S)
  rw [hmul] at hlogle
  linarith

end

end LeanArticleAudit.Pilot
