import LeanArticleAudit.Pilot.UpperBaseAdaptiveCost
import LeanArticleAudit.Pilot.UpperBaseLog

open Set
open scoped RealInnerProductSpace BigOperators

namespace LeanArticleAudit.Pilot
noncomputable section
universe u

noncomputable def baseStrongAggregateConstant (p : ℕ) : ℝ :=
  2 * (2 + 1 / Real.log 2) * (1 + baseHalvingLogConstant p) *
    (baseCoverHalvingConstant p + 1)

noncomputable def baseStrongInterfaceConstant (p : ℕ) : ℝ :=
  1 + baseStrongAggregateConstant p

theorem baseStrongAggregateConstant_nonneg (p : ℕ) :
    0 ≤ baseStrongAggregateConstant p := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 ≤ 2 + 1 / Real.log 2 := by positivity
  have hH : 0 ≤ 1 + baseHalvingLogConstant p := by
    have := baseHalvingLogConstant_pos p
    linarith
  have hC : 0 ≤ baseCoverHalvingConstant p := by
    unfold baseCoverHalvingConstant baseHalvingLeadingConstant
    have hbeta : 0 ≤ tensorBetaCoefficient p := by
      unfold tensorBetaCoefficient
      exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)
    exact mul_nonneg
      (Real.rpow_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hbeta)
          (Real.rpow_nonneg (by norm_num) _)) _)
      (Real.rpow_nonneg (pow_nonneg (by norm_num) _) _)
  unfold baseStrongAggregateConstant
  positivity

theorem baseStrongInterfaceConstant_pos (p : ℕ) :
    0 < baseStrongInterfaceConstant p := by
  unfold baseStrongInterfaceConstant
  linarith [baseStrongAggregateConstant_nonneg p]

/-- Fixed-order executable family witnessing the source class
`S_(2/(p+1),2)`. -/
noncomputable def baseStrongCertifiedFamily (p : ℕ) : StrongSolverFamily p where
  leadingConstant := baseStrongInterfaceConstant p
  leadingConstant_pos := baseStrongInterfaceConstant_pos p
  solve := fun _ _ _ _ data _ => (baseStrongSolver data).solve

theorem prop_base_strong (p : ℕ) :
    (baseStrongCertifiedFamily p).SatisfiesInterface
      (2 / ((p : ℝ) + 1)) 2 := by
  intro E instNorm instInner instFinite data hp
  constructor
  · intro G oracle center mu delta used cert hG hmu hdelta hrun
    exact baseStrongSolver_no_false_success data G oracle center mu delta used cert
      (by simpa [baseStrongCertifiedFamily, StrongSolverFamily.atData] using hrun)
  · intro G oracle center mu delta hG hmu hdelta hstrong zStar hz
    let r := ‖center.1 - zStar‖
    have hr : 0 ≤ r := norm_nonneg _
    have hrD : r ≤ data.D := by
      dsimp [r]
      simpa [dist_eq_norm] using data.diameter_le center.1 center.2 zStar hz.1
    obtain ⟨used, cert, hrun, hcert, hused⟩ :=
      baseStrongSolver_succeeds_at_first_cover data G oracle hG center mu delta
        hmu hdelta hstrong zStar hz
    have hLS := strongLog_one_le data mu delta hmu hdelta
    have hguess := adaptiveCoverCount_add_one_le_strongLog
      data mu delta r hmu hdelta hr hrD
    have hcost := adaptivePrefixCost_of_count_bounds data mu delta r center
      hmu hdelta hr hrD (strongLog data mu delta) (2 + 1 / Real.log 2)
      (baseHalvingLogConstant data.p) hLS (by
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        positivity) (baseHalvingLogConstant_pos data.p).le hguess (by
          intro k hk
          exact baseHalvingCount_cast_le_strongLog data mu delta
            (adaptiveGuessRadius data mu k) hmu hdelta
            (adaptiveGuessRadius_pos data mu hmu k).le (min_le_left _ _))
    have husedReal : (used : ℝ) ≤
        (adaptiveBaseCapFrom data mu delta center
          (adaptiveCoverCount data mu r) 0 : ℝ) := by exact_mod_cast hused
    have haggr : baseStrongAggregateConstant data.p *
          (1 + Real.rpow (data.Lp * r ^ (data.p - 1) / mu)
            (baseHalvingExponent data.p)) * (strongLog data mu delta) ^ 2 ≤
        baseStrongInterfaceConstant data.p *
          (1 + Real.rpow (data.Lp * r ^ (data.p - 1) / mu)
            (baseHalvingExponent data.p)) * (strongLog data mu delta) ^ 2 := by
      have hqbase : 0 ≤ data.Lp * r ^ (data.p - 1) / mu := by
        exact div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg hr _)) hmu.le
      have hqfac : 0 ≤ 1 + Real.rpow (data.Lp * r ^ (data.p - 1) / mu)
          (baseHalvingExponent data.p) := by
        exact add_nonneg (by norm_num) (Real.rpow_nonneg hqbase _)
      have hlead : baseStrongAggregateConstant data.p ≤
          baseStrongInterfaceConstant data.p := by
        unfold baseStrongInterfaceConstant
        linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hlead hqfac) (sq_nonneg _)
    refine ⟨used, cert, ?_, hcert, ?_⟩
    · simpa [baseStrongCertifiedFamily, StrongSolverFamily.atData] using hrun
    · change (used : ℝ) ≤ strongInterfaceCost data
        (baseStrongInterfaceConstant p) (2 / ((p : ℝ) + 1)) 2
          ‖center.1 - zStar‖ mu delta
      calc
        (used : ℝ) ≤ (adaptiveBaseCapFrom data mu delta center
            (adaptiveCoverCount data mu r) 0 : ℝ) := husedReal
        _ ≤ baseStrongAggregateConstant data.p *
            (1 + Real.rpow (data.Lp * r ^ (data.p - 1) / mu)
              (baseHalvingExponent data.p)) * (strongLog data mu delta) ^ 2 := by
          simpa [baseStrongAggregateConstant] using hcost
        _ ≤ baseStrongInterfaceConstant data.p *
            (1 + Real.rpow (data.Lp * r ^ (data.p - 1) / mu)
              (baseHalvingExponent data.p)) * (strongLog data mu delta) ^ 2 := haggr
        _ = strongInterfaceCost data (baseStrongInterfaceConstant p)
            (2 / ((p : ℝ) + 1)) 2 ‖center.1 - zStar‖ mu delta := by
          simp only [strongInterfaceCost, baseHalvingExponent]
          rw [hp]
          rfl

end
end LeanArticleAudit.Pilot

