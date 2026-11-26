import NCConcave16991.GlobalHardScoreDerivative

/-! # Actual weighted state-pressure coefficient, including every neighbor term -/

namespace NCConcave16991.GlobalHard

noncomputable section

theorem weighted_statePotentialDerivative_abs_bound {t : ℝ} (ht : t ≤ 1) :
    |t * statePotentialDerivative t| ≤ radialSlope := by
  by_cases hl : t ≤ 1 / 10
  · rw [statePotentialDerivative_left hl]
    norm_num [radialSlope]
  · have ht' : |t| ≤ 1 := by rw [abs_of_pos (by linarith)]; exact ht
    have hV : |statePotentialDerivative t| ≤ radialSlope := by
      rw [abs_le]
      exact ⟨(statePotentialDerivative_bounds t).1, (statePotentialDerivative_bounds t).2.trans (by norm_num [radialSlope])⟩
    exact (abs_product_bound _ _ 1 radialSlope (by norm_num) ht' hV).trans_eq (by ring)

def stateScoreCoefficient (previous current next entry exitValue nextEntry nextExit : ℝ) : ℝ :=
  -gamma * activation current * activationDerivative current + statePotentialDerivative current +
    incomingScoreDerivative previous current entry exitValue + outgoingScoreDerivative current next nextEntry nextExit

/-- The source's explicit 138233 bound is derived from the literal
activation/potential and both actual neighboring score derivatives. -/
theorem weighted_stateScoreCoefficient_abs_bound
    (previous current next entry exitValue nextEntry nextExit : ℝ) (ht : current ≤ 1)
    (he : |entry| ≤ 42) (hx : |exitValue| ≤ 840) (he' : |nextEntry| ≤ 42) (hx' : |nextExit| ≤ 840) :
    |current * stateScoreCoefficient previous current next entry exitValue nextEntry nextExit| ≤ 138233 := by
  have h1 := abs_product_bound (-gamma) (current * activation current * activationDerivative current) 4300 17
    (by norm_num) (by norm_num [gamma]) (weighted_activation_product_bound ht)
  have h2 := weighted_statePotentialDerivative_abs_bound ht
  have h3 := weighted_totalScoreDerivative_abs_bound previous current next entry exitValue nextEntry nextExit he hx he' hx'
  have hEq : current * stateScoreCoefficient previous current next entry exitValue nextEntry nextExit =
      -gamma * (current * activation current * activationDerivative current) + current * statePotentialDerivative current +
        current * (incomingScoreDerivative previous current entry exitValue + outgoingScoreDerivative current next nextEntry nextExit) := by
    dsimp [stateScoreCoefficient]
    ring
  rw [hEq]
  have htri := (abs_add_le (-gamma * (current * activation current * activationDerivative current) +
    current * statePotentialDerivative current)
    (current * (incomingScoreDerivative previous current entry exitValue + outgoingScoreDerivative current next nextEntry nextExit))).trans
      (add_le_add (abs_add_le _ _) le_rfl)
  norm_num [radialSlope] at h2
  rw [← abs_mul] at h2
  nlinarith

theorem stateScoreCoefficient_negative_nonpos
    (previous current next entry exitValue nextEntry nextExit : ℝ) (ht : current ≤ 0) :
    stateScoreCoefficient previous current next entry exitValue nextEntry nextExit ≤ 0 := by
  have hA := activation_zero (ht.trans deltaGate_pos.le)
  have hV := statePotentialDerivative_left (by linarith : current ≤ 1 / 10)
  simp only [stateScoreCoefficient, hA, hV, mul_zero, zero_mul, zero_add]
  exact totalScoreDerivative_low_nonpos _ _ _ _ _ _ _ (by linarith)

end

end NCConcave16991.GlobalHard
