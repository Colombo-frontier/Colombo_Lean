import NCBall.VerifiedFamily
import NCBall.ClarkeLower
import NCBall.GoldsteinParameters

/-! # A verified bounded-domain family for the Clarke Goldstein lower bound -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NCBall

theorem goldstein_family_of_absolute {n : ℕ} {ε δ Δ L : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hΔ : 0 ≤ Δ) (hL : 0 < L)
    (hsmall : ε ≤ lowerConstant * L)
    (hlarge : regimeConstant * δ * ε ≤ Δ)
    (hd : regimeConstant * Real.log (2 + Δ * L ^ 2 / (δ * ε ^ 3)) ≤ (n : ℝ) + 1)
    (u : HiddenTable n (calibratedDepth (4 * (2 * ε)) (ε / δ) Δ))
    (hu : u ∈ goodHiddenFamily n (2 * ε) (ε / δ) Δ) :
    SmoothStochasticClass (gaussianRooms n (calibratedDepth (4 * (2 * ε)) (ε / δ) Δ))
      (familyPopulation (2 * ε) (ε / δ) Δ u) (familySample (2 * ε) (ε / δ) Δ L u)
      (sampleLipschitzModulus (4 * (2 * ε)) L) (calibratedRadius (2 * ε) (ε / δ) Δ)
      (ε / δ) L Δ := by
  have hdim := goldstein_dimension_of_absolute hε hδ hΔ hd
  have hscale := goldstein_scale_of_absolute hε hsmall
  have hregime := goldstein_regime_of_absolute hε hδ hlarge
  have hq := calibratedCharges_pos hdim.1 (by positivity : 0 < 4 * (2 * ε)) hscale
  have hlog := calibrated_dimension_condition (by positivity : 0 < 2 * ε)
    (by positivity : 0 < ε / δ) hΔ hdim.2
  exact calibrated_class_verified hdim.1 (by positivity) (by positivity) hΔ hL.le
    hregime hscale (dimension_good_log hq hlog) _ (fixedDirections_clock _ u) hu

universe u

theorem bounded_goldstein_lower_bound {n : ℕ} {ε δ Δ L : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hΔ : 0 ≤ Δ) (hL : 0 < L)
    (hsmall : ε ≤ lowerConstant * L)
    (hlarge : regimeConstant * δ * ε ≤ Δ)
    (hd : regimeConstant * Real.log (2 + Δ * L ^ 2 / (δ * ε ^ 3)) ≤ (n : ℝ) + 1) :
    ∃ radius : ℝ, 0 < radius ∧
      (37 / 800) * (Δ / ε) ≤ radius ∧ radius ≤ (37 / 400) * (Δ / ε) ∧
      (∀ u ∈ goodHiddenFamily n (2 * ε) (ε / δ) Δ,
        SmoothStochasticClass (gaussianRooms n (calibratedDepth (4 * (2 * ε)) (ε / δ) Δ))
          (familyPopulation (2 * ε) (ε / δ) Δ u) (familySample (2 * ε) (ε / δ) Δ L u)
          (sampleLipschitzModulus (4 * (2 * ε)) L) radius (ε / δ) L Δ) ∧
      (∀ (Seed : Type u) [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
        (K N : ℕ) (p : RoomQueryPolicy Seed n K)
        (out : LinearHistory Seed N → Space n), Measurable out →
        (∀ u ∈ goodHiddenFamily n (2 * ε) (ε / δ) Δ,
          (1 / 2 : ℝ≥0∞) ≤ (ν.prod (sampleTableLaw n K (calibratedDepth (4 * (2 * ε)) (ε / δ) Δ)))
            {rz | experimentFromSplit (u, rz) ∈ fullClarkeSuccess p
              (calibratedRho (4 * (2 * ε)) (ε / δ)) (2 * ε) (L / (4 * (2 * ε)))
              (Real.sqrt (n : ℝ))⁻¹ δ ε N out}) →
        lowerConstant * (((n : ℝ) + 1) * L ^ 2 * Δ / (δ * ε ^ 3)) ≤ N) := by
  have hdim := goldstein_dimension_of_absolute hε hδ hΔ hd
  have hscale := goldstein_scale_of_absolute hε hsmall
  have hregime := goldstein_regime_of_absolute hε hδ hlarge
  have hγ : 0 < 4 * (2 * ε) := by positivity
  have hρ := calibratedRho_pos hγ (by positivity : 0 < ε / δ)
  have hM := calibratedDepth_ge_two hγ hregime
  have hr := calibrated_radius_bounds hγ (by positivity : 0 < ε / δ) hΔ hregime
  refine ⟨calibratedRadius (2 * ε) (ε / δ) Δ, ?_, ?_, ?_, ?_, ?_⟩
  · unfold calibratedRadius
    have : (0 : ℝ) < calibratedDepth (4 * (2 * ε)) (ε / δ) Δ := by
      exact_mod_cast (show 0 < calibratedDepth (4 * (2 * ε)) (ε / δ) Δ by omega)
    positivity
  · convert hr.1 using 1; ring
  · convert hr.2 using 1; ring
  · exact fun u hu => goldstein_family_of_absolute hε hδ hΔ hL hsmall hlarge hd u hu
  · intro Seed _ ν _ K N p out hout hsuccess
    have hs := hsuccess
    simp only [fullClarkeSuccess_eq] at hs
    have hb := goldstein_scalar_evaluation_lower_bound ν p hdim.1 hε hδ hΔ hL
      hregime hscale hdim.2 out hout hs
    exact (goldstein_coefficient_of_absolute hε hδ hΔ).trans hb

end NCBall
