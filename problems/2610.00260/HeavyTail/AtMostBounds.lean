import HeavyTail.AtMostModel
import HeavyTail.GaussianModelLower
import HeavyTail.ConfidenceKernelLower
import HeavyTail.ZeroQueryModel

/-! The concrete Gaussian, confidence and zero-query bounds with exactly the
manuscript's almost-sure, at-most-T raw-call semantics. -/
noncomputable section
open scoped ENNReal
namespace HeavyTail

theorem gaussian_atMostCallMinimax_lower_of_dimension {d : ℕ} (θ : OracleParameters)
    (hT : 0 < θ.T) (hdim : Nat.ceil (θ.L ^ 2 / θ.s ^ 2) ≤ d) :
    ENNReal.ofReal (GaussianLower.traceRate θ.μ θ.D θ.G θ.L θ.T) ≤
      atMostCallMinimax (HardSpace d) θ := by
  rw [atMostCallMinimax_eq_fixedCallMinimax]
  exact GaussianLower.gaussian_fixedCallMinimax_lower_of_dimension θ hT hdim

theorem confidence_atMostCallMinimax_lower {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (θ : OracleParameters) (e : E) (he : ‖e‖ = 1) (hT : 0 < θ.T) :
    ENNReal.ofReal (confidenceRate θ.μ θ.D θ.G θ.s θ.p θ.δ θ.T) ≤ atMostCallMinimax E θ := by
  rw [atMostCallMinimax_eq_fixedCallMinimax]
  exact confidence_fixedCallMinimax_lower θ e he hT

theorem zero_query_atMostCallMinimax_cap {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (θ : OracleParameters) :
    atMostCallMinimax E θ ≤ ENNReal.ofReal (2 * envelope θ.μ θ.D θ.G) := by
  rw [atMostCallMinimax_eq_fixedCallMinimax]
  exact zero_query_fixedCallMinimax_cap θ

theorem confidence_zero_query_atMostCallMinimax_lower {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (θ : OracleParameters) (e : E) (he : ‖e‖ = 1) (hT : θ.T = 0) :
    ENNReal.ofReal (envelope θ.μ θ.D θ.G) ≤ atMostCallMinimax E θ := by
  rw [atMostCallMinimax_eq_fixedCallMinimax]
  exact confidence_zero_query_fixedCallMinimax_lower θ e he hT

end HeavyTail
