import RandomizedFO2003.GateDerivativeBounds
import RandomizedFO2003.CascadeParameters

namespace RandomizedFO2003.Cascade

open Primitives

/-- Numerical constants for derivatives of the constructed gate after the
paper's length scale `h / γ` is factored out. -/
noncomputable def gateScaleConstant (n : ℕ) : ℝ :=
  n.factorial * gateJetConstant n * (radiusCoefficient⁻¹ + 64 * radialDerivativeJetConstant n) ^ n

theorem gateScaleConstant_pos (n : ℕ) : 0 < gateScaleConstant n := by
  have hg := gateJetConstant_pos n
  have hr := radialDerivativeJetConstant_pos n
  have hB := radiusCoefficient_pos
  unfold gateScaleConstant
  positivity

noncomputable def forceScaleConstant (n : ℕ) : ℝ :=
  if n = 0 then forcingAmplitude else saturationDerivativeConstant n

theorem forceScaleConstant_pos (n : ℕ) : 0 < forceScaleConstant n := by
  unfold forceScaleConstant
  split_ifs
  · norm_num [forcingAmplitude]
  · exact saturationDerivativeConstant_pos n

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual gate at the fixed cascade scales has uniformly bounded jets,
with its `n`-th derivative proportional to `(γ / h)^n`. -/
theorem scaled_gate_derivative_bound (n : ℕ) (a : E) (ha : ‖a‖ ≤ 1)
    {h γ : ℝ} (hh : 0 < h) (hγ : 0 < γ) (x : E) :
    ‖iteratedFDeriv ℝ n (radialGate a (radiusCoefficient * h / γ) (h / (64 * γ))) x‖ ≤
      gateScaleConstant n * (γ / h) ^ n := by
  have hB : 0 < radiusCoefficient * h / γ := div_pos (mul_pos radiusCoefficient_pos hh) hγ
  have hα : 0 < h / (64 * γ) := by positivity
  apply (radialGate_iteratedFDeriv_bound n a ha hB hα x).trans_eq
  have hs : readoutPowerConstant n (radiusCoefficient * h / γ) (h / (64 * γ)) /
      (radiusCoefficient * h / γ) =
      (radiusCoefficient⁻¹ + 64 * radialDerivativeJetConstant n) * (γ / h) := by
    unfold readoutPowerConstant
    field_simp [hh.ne', hγ.ne', radiusCoefficient_pos.ne']
    ring
  rw [hs, mul_pow]
  unfold gateScaleConstant
  ring

/-- All orders, including the bounded value at order zero. The constants
precede the dimension, direction, and scales. -/
theorem scaled_forcing_derivative_bound (n : ℕ) (b : E) {h γ : ℝ}
    (hh : 0 < h) (hγ : 0 < γ) (hb : ‖b‖ ≤ h) (x : E) :
    ‖iteratedFDeriv ℝ n (forcing b (h ^ 2 / γ) forcingOffset saturationThreshold) x‖ ≤
      forceScaleConstant n * (h ^ 2 / γ) * (γ / h) ^ n := by
  have hD : 0 < h ^ 2 / γ := by positivity
  by_cases hn : n = 0
  · subst n
    rw [norm_iteratedFDeriv_zero]
    obtain ⟨hl, hu⟩ := forcing_bounds (K := saturationThreshold) (C₀ := forcingOffset) b hD.le
      (by norm_num [saturationThreshold]) (by norm_num [saturationThreshold, forcingOffset]) x
    rw [Real.norm_eq_abs, abs_of_nonneg (hD.le.trans hl)]
    norm_num [forceScaleConstant, forcingOffset, saturationThreshold, forcingAmplitude] at hu ⊢
    nlinarith only [hu]
  · have hpos : 1 ≤ n := by omega
    calc
      _ ≤ (h ^ 2 / γ) * saturationDerivativeConstant n * (‖b‖ / (h ^ 2 / γ)) ^ n :=
        forcing_iteratedFDeriv_bound n hpos b hD (by norm_num [saturationThreshold]) forcingOffset x
      _ ≤ (h ^ 2 / γ) * saturationDerivativeConstant n * (h / (h ^ 2 / γ)) ^ n := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD.le (saturationDerivativeConstant_pos n).le)
        exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hb hD.le) n
      _ = forceScaleConstant n * (h ^ 2 / γ) * (γ / h) ^ n := by
        have hs : h / (h ^ 2 / γ) = γ / h := by field_simp; ring
        rw [hs, forceScaleConstant, if_neg hn]
        ring

end RandomizedFO2003.Cascade
