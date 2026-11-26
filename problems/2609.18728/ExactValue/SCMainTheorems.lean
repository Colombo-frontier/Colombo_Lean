import ExactValue.SCUpperBound
import ExactValue.SCRegions

open scoped ENNReal
set_option autoImplicit false
namespace ExactValue
noncomputable section

theorem relative_accuracy_identity {μ β R ε : ℝ} (hμ : 0 < μ) (hβ : 0 < β) :
    (β * R ^ 2 / ε) / (β / μ) = μ * R ^ 2 / ε := by
  by_cases hε : ε = 0
  · simp [hε]
  · field_simp [hβ.ne', hμ.ne', hε]
    ring

/-- Both minimax bounds throughout the complete certified near-optimal region. -/
theorem sc_near_optimal_region {d : ℕ} (hd : 8 ≤ d) {μ β R ε : ℝ}
    (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R) (hε : 0 < ε)
    (hεmax : ε ≤ β * R ^ 2 / 64)
    (hreg : min (β * R ^ 2 / ε) (β / μ) ≤ dimensionScale d ^ 2) :
    ENNReal.ofReal ((1 / 8192 : ℝ) * d * Real.sqrt (min (β * R ^ 2 / ε) (β / μ))) ≤
      scValueComplexity d R μ β ε ∧
    scValueComplexity d R μ β ε ≤ ENNReal.ofReal (36 * d *
      Real.sqrt (min (β * R ^ 2 / ε) (β / μ)) * (1 + logPlus (μ * R ^ 2 / ε))) := by
  refine ⟨sc_near_lower hd hμ hμβ hR hε hεmax hreg, ?_⟩
  have hβ := hμ.trans_le hμβ
  rcases le_total (β * R ^ 2 / ε) (β / μ) with h | h
  · rw [min_eq_left h]
    have hmax : ε ≤ β * R ^ 2 := by nlinarith [mul_pos hβ (sq_pos_of_pos hR)]
    apply (sc_direct_upper (by omega) hβ hR hε hmax).trans
    apply ENNReal.ofReal_le_ofReal
    have hp : 0 ≤ logPlus (μ * R ^ 2 / ε) := le_max_left _ _
    have hs : 0 ≤ (d : ℝ) * Real.sqrt (β * R ^ 2 / ε) := by positivity
    nlinarith [mul_nonneg hs hp]
  · rw [min_eq_right h]
    exact sc_restarted_upper (by omega) hμ hμβ hR hε

/-- The high-accuracy branch holds for every epsilon below a fixed relative threshold. -/
theorem sc_full_high_accuracy {d : ℕ} (hd : 8 ≤ d) {μ β R ε : ℝ}
    (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R) (hε : 0 < ε)
    (hεmax : ε ≤ μ * R ^ 2 / 64) (hκD : β / μ ≤ dimensionScale d ^ 2) :
    ENNReal.ofReal ((1 / 8192 : ℝ) * d * Real.sqrt (β / μ)) ≤ scValueComplexity d R μ β ε ∧
      scValueComplexity d R μ β ε ≤
        ENNReal.ofReal (36 * d * Real.sqrt (β / μ) * (1 + Real.log (μ * R ^ 2 / ε))) := by
  refine ⟨sc_high_accuracy_lower hd hμ hμβ hR hε hεmax hκD, ?_⟩
  have hz : 1 ≤ μ * R ^ 2 / ε := by
    apply (one_le_div hε).mpr
    nlinarith [mul_pos hμ (sq_pos_of_pos hR)]
  have hlog := Real.log_nonneg hz
  simpa only [logPlus, max_eq_right hlog] using sc_restarted_upper (d := d) (by omega) hμ hμβ hR hε

/-- Numerical witnesses for the universal constants in the combined main theorems. -/
theorem sc_main_bounds {d : ℕ} (hd : 8 ≤ d) {μ β R ε : ℝ}
    (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R) (hε : 0 < ε) (hεmax : ε ≤ β * R ^ 2 / 64) :
    ENNReal.ofReal ((1 / 8192 : ℝ) * d * scLowerScale d μ β R ε) ≤ scValueComplexity d R μ β ε ∧
      scValueComplexity d R μ β ε ≤ ENNReal.ofReal (36 * d *
        min (Real.sqrt (β * R ^ 2 / ε)) (Real.sqrt (β / μ) * (1 + logPlus (μ * R ^ 2 / ε)))) := by
  refine ⟨sc_fixed_parameter_lower hd hμ hμβ hR hε hεmax, ?_⟩
  apply sc_combined_upper (by omega) hμ hμβ hR hε
  have hβ := hμ.trans_le hμβ
  nlinarith [mul_pos hβ (sq_pos_of_pos hR)]

end
end ExactValue
