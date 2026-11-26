import ExactValue.SCMainTheorems
import ExactValue.ZeroDimension

open scoped ENNReal
set_option autoImplicit false
namespace ExactValue
noncomputable section

theorem scValueComplexity_zero_dimension {μ β R ε : ℝ} (hR : 0 ≤ R) (hε : 0 ≤ ε) :
    scValueComplexity 0 R μ β ε = 0 := by
  apply le_antisymm _ (zero_le _)
  exact scValueComplexity_le_convex.trans (valueComplexity_zero_dimension hR hε).le

theorem sc_combined_upper_all_dimensions (d : ℕ) {μ β R ε : ℝ}
    (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R) (hε : 0 < ε) (hεmax : ε ≤ β * R ^ 2) :
    scValueComplexity d R μ β ε ≤ ENNReal.ofReal (36 * d *
      min (Real.sqrt (β * R ^ 2 / ε)) (Real.sqrt (β / μ) * (1 + logPlus (μ * R ^ 2 / ε)))) := by
  cases d with
  | zero => rw [scValueComplexity_zero_dimension hR.le hε.le]; positivity
  | succ d => exact sc_combined_upper (Nat.succ_pos d) hμ hμβ hR hε hεmax

theorem sc_direct_upper_calls {d : ℕ} (hd : 0 < d) {μ β R ε : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hε : 0 < ε) (hεmax : ε ≤ β * R ^ 2) :
    scValueComplexity d R μ β ε ≤ ((d + 1) * upperIterationCount β R ε : ℕ) :=
  scValueComplexity_le_convex.trans (valueComplexity_upper_calls hd hβ hR hε hεmax)

end
end ExactValue
