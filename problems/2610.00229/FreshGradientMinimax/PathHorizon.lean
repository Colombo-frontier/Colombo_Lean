import FreshGradientMinimax.PathHardGap
import FreshGradientMinimax.PathEnergyFormula

/-! The horizon-specific path length and center cut, with actual membership
in the localized and unlocalized instance classes. The distributional hiding
argument is separate and is not assumed or claimed here. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def pathHorizonObjective (p : Parameters) (hκ : 4 * p.μ ≤ p.L) (N : ℕ) {dy : ℕ}
    (V : Euclid (4 * N + 4) →ₗᵢ[ℝ] Euclid dy) (s : ℝ) (hs : s ^ 2 = 1) : NCObjective 1 dy p.L p.μ :=
  pathHardObjective (n := 4 * N + 3) V (2 * N + 2) s p.L p.μ p.ε p.μ_pos hκ p.ε_pos hs

theorem pathHorizonObjective_initial_residual (p : Parameters) (hκ : 4 * p.μ ≤ p.L) (N : ℕ) {dy : ℕ}
    (V : Euclid (4 * N + 4) →ₗᵢ[ℝ] Euclid dy) (s : ℝ) (hs : s ^ 2 = 1) :
    ‖(pathHorizonObjective p hκ N V s hs).gradY 0 0‖ = pathHardSignal p.L p.μ p.ε (4 * N + 3) :=
  pathHardObjective_initial_residual V (2 * N + 2) s p.L p.μ p.ε p.μ_pos hκ p.ε_pos hs

theorem pathHorizonObjective_gap (p : Parameters) (hκ : 4 * p.μ ≤ p.L) (N : ℕ) {dy : ℕ}
    (V : Euclid (4 * N + 4) →ₗᵢ[ℝ] Euclid dy) (s : ℝ) (hs : s ^ 2 = 1) :
    (pathHorizonObjective p hκ N V s hs).PrimalGapAtMost (80 * p.ε ^ 2 / p.L) :=
  pathHardObjective_gap V (by omega : 0 < 2 * N + 2) (by omega : 2 * N + 2 ≤ 4 * N + 3)
    s p.L p.μ p.ε p.μ_pos hκ p.ε_pos hs

theorem pathHorizonObjective_inClass (p : Parameters) (hκ : 4 * p.μ ≤ p.L) (N : ℕ)
    (hgap : 80 * p.ε ^ 2 / p.L ≤ p.gap) (hG : pathHardSignal p.L p.μ p.ε (4 * N + 3) ≤ p.G)
    {dy : ℕ} (V : Euclid (4 * N + 4) →ₗᵢ[ℝ] Euclid dy) (s : ℝ) (hs : s ^ 2 = 1) :
    InLocalizedClass (pathHorizonObjective p hκ N V s hs) p.gap (some p.G) := by
  constructor
  · intro x
    exact (pathHorizonObjective_gap p hκ N V s hs x).trans hgap
  · simpa only [NCObjective.DualLocalized, pathHorizonObjective_initial_residual] using hG

theorem pathHorizonObjective_unlocalized (p : Parameters) (hκ : 4 * p.μ ≤ p.L) (N : ℕ)
    (hgap : 80 * p.ε ^ 2 / p.L ≤ p.gap)
    {dy : ℕ} (V : Euclid (4 * N + 4) →ₗᵢ[ℝ] Euclid dy) (s : ℝ) (hs : s ^ 2 = 1) :
    InLocalizedClass (pathHorizonObjective p hκ N V s hs) p.gap none := by
  refine ⟨fun x => (pathHorizonObjective_gap p hκ N V s hs x).trans hgap, trivial⟩

theorem pathHorizonObjective_success_disjoint (p : Parameters) (hκ : 4 * p.μ ≤ p.L) (N : ℕ) {dy dz : ℕ}
    (V : Euclid (4 * N + 4) →ₗᵢ[ℝ] Euclid dy) (W : Euclid (4 * N + 4) →ₗᵢ[ℝ] Euclid dz) :
    Disjoint ((pathHorizonObjective p hκ N V 1 (by norm_num)).successSet p.ε)
      ((pathHorizonObjective p hκ N W (-1) (by norm_num)).successSet p.ε) :=
  pathHardObjective_success_disjoint V W (by omega : 0 < 2 * N + 2)
    (by omega : 2 * N + 2 ≤ 4 * N + 3) p.L p.μ p.ε p.μ_pos hκ p.ε_pos

end FreshGradientMinimax
