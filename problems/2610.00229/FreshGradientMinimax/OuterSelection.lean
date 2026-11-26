import FreshGradientMinimax.OuterParameters
import FreshGradientMinimax.UniformMeasure

/-! The law of a uniform independent choice of a completed coarse solve.
It preserves the actual solve's center and primal/dual output together. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators

def selectedOuterLaw {dx dy : ℕ} (L σ μ Δ G η : ℝ) (T : ℕ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) : Measure (Euclid dx × Joint dx dy) :=
  uniformMeasure (fun j => localizedOuterLaw L σ μ Δ G η T K (j + 1)) T

theorem selectedOuterLaw_probability {dx dy : ℕ} (L σ μ Δ G η : ℝ) {T : ℕ} (hT : 0 < T)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] :
    IsProbabilityMeasure (selectedOuterLaw L σ μ Δ G η T K) := uniformMeasure_probability _ hT

namespace NCObjective
variable {dx dy : ℕ} {L μ σ : ℝ} (F : NCObjective dx dy L μ)

theorem selectedOuterLaw_moments (O : FreshOracle F σ) {Δ G η : ℝ}
    (hΔ : F.PrimalGapAtMost Δ) (hG : F.DualLocalized G) (hη : 0 < η) {T : ℕ} (hT : 0 < T) :
    Integrable F.proximalStartEnergy (selectedOuterLaw L σ μ Δ G η T O.kernel) ∧
    (∫ p, F.proximalStartEnergy p ∂selectedOuterLaw L σ μ Δ G η T O.kernel) ≤ 6 * η ∧
    Integrable (fun p : Euclid dx × Joint dx dy => F.proximalResidualEnergy p.1)
      (selectedOuterLaw L σ μ Δ G η T O.kernel) ∧
    (∫ p, F.proximalResidualEnergy p.1 ∂selectedOuterLaw L σ μ Δ G η T O.kernel) ≤ Δ / T + η := by
  have he (j : ℕ) (hj : j < T) := F.localizedOuter_refinement_energy O hΔ hG hη T hj
  have hr (j : ℕ) (hj : j < T) := (F.localizedOuter_step_moments O hΔ hG hη T hj).2
  refine ⟨uniformMeasure_integrable _ _ _ (fun j hj => (he j hj).1),
    uniformMeasure_mean_bound _ hT _ (fun j hj => (he j hj).1) (fun j hj => (he j hj).2),
    uniformMeasure_integrable _ _ _ hr, ?_⟩
  rw [selectedOuterLaw, uniformMeasure_integral _ _ _ hr]
  have ht : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  apply (div_le_iff₀ ht).mpr
  rw [show (Δ / T + η) * T = Δ + T * η by field_simp; ring]
  exact F.localizedOuter_residual_bound O hΔ hG hη T

end NCObjective
end FreshGradientMinimax
