import ExactValue.SCLowerBound

open scoped ENNReal
set_option autoImplicit false
namespace ExactValue
noncomputable section

/-- The accuracy-dominated branch matches up to explicit universal constants. -/
theorem sc_accuracy_branch {d : ℕ} (hd : 8 ≤ d) {μ β R ε : ℝ}
    (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R) (hε : 0 < ε)
    (hεmax : ε ≤ β * R ^ 2 / 64)
    (hQκ : β * R ^ 2 / ε ≤ β / μ)
    (hQD : β * R ^ 2 / ε ≤ dimensionScale d ^ 2) :
    ENNReal.ofReal ((1 / 8192 : ℝ) * d * Real.sqrt (β * R ^ 2 / ε)) ≤ scValueComplexity d R μ β ε ∧
      scValueComplexity d R μ β ε ≤ ENNReal.ofReal (6 * d * Real.sqrt (β * R ^ 2 / ε)) := by
  have hβ := hμ.trans_le hμβ
  have hsD : Real.sqrt (β * R ^ 2 / ε) ≤ dimensionScale d :=
    (Real.sqrt_le_left (dimensionScale_pos (by omega)).le).mpr hQD
  have hsκ := Real.sqrt_le_sqrt hQκ
  constructor
  · simpa only [scLowerScale, min_eq_left hsκ, min_eq_left hsD] using
      sc_fixed_parameter_lower hd hμ hμβ hR hε hεmax
  · apply sc_direct_upper (by omega) hβ hR hε
    nlinarith [mul_pos hβ (sq_pos_of_pos hR)]

theorem sc_high_accuracy_lower {d : ℕ} (hd : 8 ≤ d) {μ β R ε : ℝ}
    (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R) (hε : 0 < ε)
    (hεmax : ε ≤ μ * R ^ 2 / 64)
    (hκD : β / μ ≤ dimensionScale d ^ 2) :
    ENNReal.ofReal ((1 / 8192 : ℝ) * d * Real.sqrt (β / μ)) ≤ scValueComplexity d R μ β ε := by
  have hβ := hμ.trans_le hμβ
  have hεβ : ε ≤ β * R ^ 2 / 64 := by
    have := mul_le_mul_of_nonneg_right hμβ (sq_nonneg R)
    linarith
  have hQκ : β / μ ≤ β * R ^ 2 / ε := by
    apply (div_le_div_iff₀ hμ hε).mpr
    have hsmall : ε ≤ μ * R ^ 2 := by nlinarith [mul_pos hμ (sq_pos_of_pos hR)]
    nlinarith [mul_le_mul_of_nonneg_left hsmall hβ.le]
  have hsκ := Real.sqrt_le_sqrt hQκ
  have hsD : Real.sqrt (β / μ) ≤ dimensionScale d :=
    (Real.sqrt_le_left (dimensionScale_pos (by omega)).le).mpr hκD
  simpa only [scLowerScale, min_eq_right hsκ, min_eq_left hsD] using
    sc_fixed_parameter_lower hd hμ hμβ hR hε hεβ

theorem sc_near_lower {d : ℕ} (hd : 8 ≤ d) {μ β R ε : ℝ}
    (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R) (hε : 0 < ε)
    (hεmax : ε ≤ β * R ^ 2 / 64)
    (hreg : min (β * R ^ 2 / ε) (β / μ) ≤ dimensionScale d ^ 2) :
    ENNReal.ofReal ((1 / 8192 : ℝ) * d * Real.sqrt (min (β * R ^ 2 / ε) (β / μ))) ≤
      scValueComplexity d R μ β ε := by
  have hsD : Real.sqrt (min (β * R ^ 2 / ε) (β / μ)) ≤ dimensionScale d :=
    (Real.sqrt_le_left (dimensionScale_pos (by omega)).le).mpr hreg
  have hsmin : min (Real.sqrt (β * R ^ 2 / ε)) (Real.sqrt (β / μ)) =
      Real.sqrt (min (β * R ^ 2 / ε) (β / μ)) := by
    rcases le_total (β * R ^ 2 / ε) (β / μ) with h | h
    · rw [min_eq_left h, min_eq_left (Real.sqrt_le_sqrt h)]
    · rw [min_eq_right h, min_eq_right (Real.sqrt_le_sqrt h)]
  simpa only [scLowerScale, hsmin, min_eq_left hsD] using
    sc_fixed_parameter_lower hd hμ hμβ hR hε hεmax

end
end ExactValue
