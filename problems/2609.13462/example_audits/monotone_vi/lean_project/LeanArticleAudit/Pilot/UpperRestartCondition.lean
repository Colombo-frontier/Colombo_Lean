import LeanArticleAudit.Pilot.UpperRestartTransformation

/-!
# Radius and condition-number bounds for certified restart

This file isolates the scalar bounds for the radii used by one scheduled
restart trial.  It intentionally does not alter the executable restart,
cost, or logarithmic-accounting modules.
-/

namespace LeanArticleAudit.Pilot

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every radius through the public stopping index is positive and no larger
than the initial supplied radius. -/
theorem restartRadius_pos_le_initial
    (mu delta R : ℝ) (hR : 0 < R)
    (i : ℕ) (hi : i ≤ restartHalvingCount mu delta R) :
    0 < R / (2 : ℝ) ^ i ∧ R / (2 : ℝ) ^ i ≤ R := by
  have _ := hi
  constructor
  · exact div_pos hR (pow_pos (by norm_num) i)
  · exact div_le_self hR.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

/-- At every nonfinal stage the residual condition has the exact cancellation
from the source and is bounded by its value at the initial radius. -/
theorem restartResidualCondition_nonfinal
    (data : VIPublicData E) (mu delta R : ℝ)
    (hmu : 0 < mu) (hdelta : 0 < delta) (hR : 0 < R)
    (i : ℕ) (hi : i < restartHalvingCount mu delta R) :
    residualCondition data (R / (2 : ℝ) ^ i)
        (mu * (R / (2 : ℝ) ^ i) / 2) =
          2 * data.Lp * (R / (2 : ℝ) ^ i) ^ (data.p - 1) / mu ∧
    residualCondition data (R / (2 : ℝ) ^ i)
        (mu * (R / (2 : ℝ) ^ i) / 2) ≤
          2 * data.Lp * R ^ (data.p - 1) / mu := by
  have hirange := restartRadius_pos_le_initial mu delta R hR i hi.le
  have hid := residualCondition_restart_accuracy data mu
    (R / (2 : ℝ) ^ i) hmu hirange.1
  refine ⟨hid, ?_⟩
  rw [hid]
  have hpow : (R / (2 : ℝ) ^ i) ^ (data.p - 1) ≤
      R ^ (data.p - 1) := by
    exact pow_le_pow_left₀ hirange.1.le hirange.2 _
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow
      (mul_nonneg (by norm_num) data.Lp_pos.le))
    hmu.le

/-- At the least stopping index, the threshold accuracy controls the final
residual condition by the same initial-radius condition number. -/
theorem restartResidualCondition_final
    (data : VIPublicData E) (mu delta R : ℝ)
    (hmu : 0 < mu) (hdelta : 0 < delta) (hR : 0 < R) :
    residualCondition data
        (R / (2 : ℝ) ^ restartHalvingCount mu delta R) delta ≤
      2 * data.Lp * R ^ (data.p - 1) / mu := by
  let n := restartHalvingCount mu delta R
  let r := R / (2 : ℝ) ^ n
  have hrange : 0 < r ∧ r ≤ R := by
    dsimp [r, n]
    exact restartRadius_pos_le_initial mu delta R hR _ le_rfl
  have hthreshold : mu * r / 2 ≤ delta := by
    dsimp [r, n]
    exact restartHalvingCount_threshold mu delta R hmu hdelta hR.le
  have hp : 1 ≤ data.p := le_trans (by omega : 1 ≤ 2) data.p_ge_two
  have hpow : r ^ (data.p - 1) ≤ R ^ (data.p - 1) :=
    pow_le_pow_left₀ hrange.1.le hrange.2 _
  have hfactor : 0 ≤ 2 * data.Lp * R ^ (data.p - 1) / mu :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) data.Lp_pos.le)
        (pow_nonneg hR.le _)) hmu.le
  rw [residualCondition]
  apply (div_le_iff₀ hdelta).2
  have hscale := mul_le_mul_of_nonneg_left hthreshold hfactor
  have hradial : data.Lp * r ^ data.p ≤
      (2 * data.Lp * R ^ (data.p - 1) / mu) * (mu * r / 2) := by
    rw [show r ^ data.p = r ^ (data.p - 1) * r by
      rw [← pow_succ]; congr; omega]
    have hr0 := hrange.1.le
    have hmul := mul_le_mul_of_nonneg_right hpow hr0
    have hLpMul := mul_le_mul_of_nonneg_left hmul data.Lp_pos.le
    calc
      data.Lp * (r ^ (data.p - 1) * r) ≤
          data.Lp * (R ^ (data.p - 1) * r) := by
            simpa [mul_assoc] using hLpMul
      _ = (2 * data.Lp * R ^ (data.p - 1) / mu) * (mu * r / 2) := by
        field_simp [hmu.ne']
  exact hradial.trans hscale

end

end LeanArticleAudit.Pilot
