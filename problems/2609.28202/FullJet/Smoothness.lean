import FullJet.Opacity
import Mathlib.Analysis.Calculus.MeanValue

open scoped ContDiff NNReal

namespace FullJet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bounded next Fréchet derivative implies Lipschitz continuity of the
current derivative in the operator norm used by the manuscript. -/
theorem lipschitz_iteratedFDeriv_of_bound {f : E → ℝ} (p : ℕ)
    (hf : ContDiff ℝ ∞ f) (C : ℝ≥0)
    (hbound : ∀ x, ‖iteratedFDeriv ℝ (p + 1) f x‖ ≤ C) :
    LipschitzWith C (iteratedFDeriv ℝ p f) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · exact hf.differentiable_iteratedFDeriv (by
      exact_mod_cast (show (p : ℕ∞) < ⊤ from WithTop.coe_lt_top p))
  · intro x
    change ‖fderiv ℝ (iteratedFDeriv ℝ p f) x‖ ≤ (C : ℝ)
    rw [norm_fderiv_iteratedFDeriv]
    exact hbound x

theorem component_smoothness_of_bound {f : E → ℝ} (p : ℕ)
    (hf : ContDiff ℝ ∞ f) (H ρ : ℝ) (hH : 0 ≤ H) (hρ : 0 < ρ)
    (hbound : ∀ x, ‖iteratedFDeriv ℝ (p + 1) f x‖ ≤ H / ρ) (x y : E) :
    ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ ≤ (H / ρ) * ‖x - y‖ := by
  let C : ℝ≥0 := ⟨H / ρ, div_nonneg hH hρ.le⟩
  exact (lipschitz_iteratedFDeriv_of_bound p hf C hbound).norm_sub_le x y

end FullJet
