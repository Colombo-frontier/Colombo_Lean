import FreshGradientMinimax.AcceleratedPhysicalModel
import FreshGradientMinimax.AcceleratedSizeBounds
import FreshGradientMinimax.Minimax

/-! The physical family belongs to the actual localized instance class
for every nonnegative localization/noise budget. This is the analytic
part of E.3, before the adaptive hiding argument. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem acceleratedPhysicalModel_in_class (p : Parameters) {n k dx dy : ℕ}
    (U : Euclid (k * 2 + 1) →ₗᵢ[ℝ] Euclid dx)
    (V : Euclid (k * (n + 2)) →ₗᵢ[ℝ] Euclid dy)
    (hn : 10 ≤ n + 2) (hk : 0 < k)
    (hchain : (n + 2 : ℝ) ^ 2 ≤ p.L / (4 * acceleratedSmoothnessConstant * p.μ))
    (hgap : 1000 * (k + 1 : ℕ) * acceleratedValueScale p.L p.ε ≤ p.gap) :
    InLocalizedClass (acceleratedPhysicalModel U V hn hk (p.μ_pos.trans_le p.μ_le_L) p.ε_pos p.μ_pos hchain)
      p.gap (some p.G) := by
  refine ⟨acceleratedPhysicalModel_gap U V hn hk _ _ _ hchain hgap, ?_⟩
  exact (acceleratedPhysicalModel_localized U V hn hk _ _ _ hchain).trans p.G_nonneg

theorem acceleratedPhysicalModel_success_excludes_hidden (p : Parameters) {n k dx dy : ℕ}
    (U : Euclid (k * 2 + 1) →ₗᵢ[ℝ] Euclid dx)
    (V : Euclid (k * (n + 2)) →ₗᵢ[ℝ] Euclid dy)
    (hn : 10 ≤ n + 2) (hk : 0 < k)
    (hchain : (n + 2 : ℝ) ^ 2 ≤ p.L / (4 * acceleratedSmoothnessConstant * p.μ))
    (x : Euclid dx)
    (hlast : |compressedCoordinates U 1 (acceleratedPrimalRadius k) ((acceleratedLengthScale p.L p.ε)⁻¹ • x)
      (interleavedZ (⟨k - 1, by omega⟩ : Fin k))| ≤ 1 / 4) :
    x ∉ (acceleratedPhysicalModel U V hn hk (p.μ_pos.trans_le p.μ_le_L) p.ε_pos p.μ_pos hchain).successSet p.ε := by
  intro hx
  change ‖gradient (acceleratedPhysicalModel U V hn hk (p.μ_pos.trans_le p.μ_le_L) p.ε_pos p.μ_pos hchain).value x‖ ≤ p.ε at hx
  rw [NCObjective.true_primal_gradient] at hx
  have h := acceleratedPhysicalModel_barrier U V hn hk (p.μ_pos.trans_le p.μ_le_L) p.ε_pos p.μ_pos hchain x hlast
  linarith only [h, hx, p.ε_pos]

theorem accelerated_physical_family (p : Parameters)
    (hκ : acceleratedConditionThreshold ≤ p.κ)
    (hgap : acceleratedGapThreshold * p.ε ^ 2 ≤ p.L * p.gap) :
    ∃ n k : ℕ, ∃ hn : 10 ≤ n + 2, ∃ hk : 0 < k,
      ∃ hchain : (n + 2 : ℝ) ^ 2 ≤ p.L / (4 * acceleratedSmoothnessConstant * p.μ),
      n + 2 = ⌊Real.sqrt (p.κ / (4 * acceleratedSmoothnessConstant))⌋₊ ∧
      k + 1 = ⌊p.gap / (1000 * acceleratedValueScale p.L p.ε)⌋₊ ∧
      (acceleratedStageCoefficient / 4) * p.deterministic ≤ ((acceleratedStageCount n k : ℝ) - 2) / 2 ∧
      ∀ dx dy : ℕ, ∀ U : Euclid (k * 2 + 1) →ₗᵢ[ℝ] Euclid dx,
        ∀ V : Euclid (k * (n + 2)) →ₗᵢ[ℝ] Euclid dy,
        let O := acceleratedPhysicalModel U V hn hk (p.μ_pos.trans_le p.μ_le_L) p.ε_pos p.μ_pos hchain
        InLocalizedClass O p.gap (some p.G) ∧
        (∀ x, |compressedCoordinates U 1 (acceleratedPrimalRadius k) ((acceleratedLengthScale p.L p.ε)⁻¹ • x)
          (interleavedZ (⟨k - 1, by omega⟩ : Fin k))| ≤ 1 / 4 → x ∉ O.successSet p.ε) ∧
        (∀ z, (FreshOracle.exact O p.σ).kernel z = MeasureTheory.Measure.dirac (O.jointGradient z)) := by
  obtain ⟨n, k, hn, hk, hnf, hkf, hc, hg, hsize⟩ := accelerated_physical_parameters p hκ hgap
  refine ⟨n, k, hn, hk, hc, hnf, hkf, hsize, ?_⟩
  intro dx dy U V
  exact ⟨acceleratedPhysicalModel_in_class p U V hn hk hc hg,
    acceleratedPhysicalModel_success_excludes_hidden p U V hn hk hc,
    FreshOracle.exact_kernel _ p.σ⟩

end FreshGradientMinimax
