import RandomizedFO2003.ScaleFloors
import RandomizedFO2003.Algebra

namespace RandomizedFO2003.Cascade

noncomputable def stageCoefficient : ℝ :=
  (curvatureCoefficient / (2 * forcingAmplitude)) * (512 : ℝ) ^ (-(3 / 2 : ℝ))

noncomputable def degreeCoefficient : ℝ :=
  (1 / 32 : ℝ) * curvatureCoefficient ^ (-(1 / 2 : ℝ)) * (512 : ℝ) ^ (-(1 / 4 : ℝ))

noncomputable def massThreshold : ℝ := 2 / stageCoefficient
noncomputable def lowerRateCoefficient : ℝ := stageCoefficient * degreeCoefficient / 4

theorem stageCoefficient_pos : 0 < stageCoefficient := by
  have hc := curvatureCoefficient_pos
  unfold stageCoefficient forcingAmplitude
  positivity

theorem degreeCoefficient_pos : 0 < degreeCoefficient := by
  have hc := curvatureCoefficient_pos
  unfold degreeCoefficient
  positivity

theorem massThreshold_pos : 0 < massThreshold := div_pos (by norm_num) stageCoefficient_pos
theorem lowerRateCoefficient_pos : 0 < lowerRateCoefficient :=
  div_pos (mul_pos stageCoefficient_pos degreeCoefficient_pos) (by norm_num)

theorem sqrt_div_sq_eq_rpow {x : ℝ} (hx : 0 < x) :
    Real.sqrt x / x ^ 2 = x ^ (-(3 / 2 : ℝ)) := by
  rw [show (-(3 / 2 : ℝ)) = (1 / 2 : ℝ) - 2 by norm_num, Real.rpow_sub hx,
    Real.rpow_two, Real.sqrt_eq_rpow]

theorem stageArgument_factorization {ε Δ L₂ : ℝ} (hε : 0 < ε) (hL₂ : 0 < L₂) :
    stageArgument ε Δ L₂ =
      stageCoefficient * (Δ * L₂ ^ (1 / 2 : ℝ) * ε ^ (-(3 / 2 : ℝ))) := by
  unfold stageArgument lowerCurvature
  rw [Real.sqrt_mul hL₂.le]
  calc
    _ = (curvatureCoefficient / (2 * forcingAmplitude)) * Δ * Real.sqrt L₂ *
        (Real.sqrt (rhsScale ε) / (rhsScale ε) ^ 2) := by ring
    _ = _ := by
      rw [sqrt_div_sq_eq_rpow (rhsScale_pos hε), Real.sqrt_eq_rpow, rhsScale,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 512) hε.le]
      unfold stageCoefficient
      ring

theorem degreeArgument_factorization {ε L₁ L₂ : ℝ} (hε : 0 < ε) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) :
    degreeArgument ε L₁ L₂ = degreeCoefficient *
      (L₁ ^ (1 / 2 : ℝ) * L₂ ^ (-(1 / 4 : ℝ)) * ε ^ (-(1 / 4 : ℝ))) := by
  have hh := rhsScale_pos hε
  have hc := curvatureCoefficient_pos
  have hfour : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by rw [← Real.sqrt_eq_rpow]; norm_num
  unfold degreeArgument upperCurvature lowerCurvature
  rw [Real.sqrt_eq_rpow, Real.div_rpow (by positivity) (by positivity),
    Real.div_rpow hL₁.le (by norm_num), hfour,
    Real.mul_rpow hc.le (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
    ← Real.rpow_mul (mul_nonneg hL₂.le hh.le)]
  norm_num only [show (1 / 2 : ℝ) * (1 / 2 : ℝ) = 1 / 4 by norm_num]
  rw [Real.mul_rpow hL₂.le hh.le, rhsScale, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 512) hε.le]
  unfold degreeCoefficient
  rw [Real.rpow_neg hc.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 512),
    Real.rpow_neg hL₂.le, Real.rpow_neg hε.le]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem stageArgument_large_of_mass {ε Δ L₂ : ℝ} (hε : 0 < ε) (hL₂ : 0 < L₂)
    (hmass : massThreshold ≤ Δ * L₂ ^ (1 / 2 : ℝ) * ε ^ (-(3 / 2 : ℝ))) :
    2 ≤ stageArgument ε Δ L₂ := by
  rw [stageArgument_factorization hε hL₂]
  have h := (div_le_iff₀ stageCoefficient_pos).mp hmass
  nlinarith only [h]

/-- The continuous stage and degree arguments give exactly the target rate,
including the fixed `h = 512ε` and curvature constants. -/
theorem stage_degree_factorization {ε Δ L₁ L₂ : ℝ} (hε : 0 < ε) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) :
    stageArgument ε Δ L₂ * degreeArgument ε L₁ L₂ =
      (stageCoefficient * degreeCoefficient) * Model.rate ε Δ L₁ L₂ := by
  rw [stageArgument_factorization hε hL₂, degreeArgument_factorization hε hL₁ hL₂]
  calc
    _ = (stageCoefficient * degreeCoefficient) *
        ((Δ * L₂ ^ (1 / 2 : ℝ) * ε ^ (-(3 / 2 : ℝ))) *
          (L₁ ^ (1 / 2 : ℝ) * L₂ ^ (-(1 / 4 : ℝ)) * ε ^ (-(1 / 4 : ℝ)))) := by ring
    _ = _ := by rw [rate_factorization ε Δ L₁ L₂ hε hL₂]; rfl

/-- Both floors have been included: a fixed positive numerical multiple of
the target rate is bounded by the actual integer stage-degree product. -/
theorem chosen_stage_degree_rate {ε Δ L₁ L₂ : ℝ} (hε : 0 < ε) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (haccuracy : ε ≤ accuracyConstant * L₁ ^ 2 / L₂)
    (hmass : massThreshold ≤ Δ * L₂ ^ (1 / 2 : ℝ) * ε ^ (-(3 / 2 : ℝ))) :
    lowerRateCoefficient * Model.rate ε Δ L₁ L₂ ≤
      ((stageIndex ε Δ L₂ * degreeCount ε L₁ L₂ : ℕ) : ℝ) := by
  have h := floored_stage_degree_lower_bound (stageArgument_large_of_mass hε hL₂ hmass)
    (degreeArgument_large hε hL₁ hL₂ haccuracy)
  rw [stage_degree_factorization hε hL₁ hL₂] at h
  convert h using 1
  unfold lowerRateCoefficient
  ring

end RandomizedFO2003.Cascade
