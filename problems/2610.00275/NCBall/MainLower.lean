import NCBall.VerifiedGoldstein
import NCBall.CountableGoldstein

/-! # Main lower bounds with a common verified family and the full sample pool

The radius and stochastic family are fixed before the algorithm. The algorithm
may choose any natural-number sample label adaptively, including unused labels,
and may reuse it arbitrarily. Each reply is one exact scalar sample evaluation.
The seed is independent of the countable iid sample pool. There is no restriction
on query locations, so the results also cover algorithms confined to the ball.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NCBall
universe u

theorem smooth_main_lower_bound {n : ℕ} {η H Δ L : ℝ}
    (hη : 0 < η) (hH : 0 < H) (hΔ : 0 ≤ Δ) (hL : 0 < L)
    (hsmall : η ≤ lowerConstant * L)
    (hlarge : regimeConstant * η ^ 2 ≤ H * Δ)
    (hd : regimeConstant * Real.log (2 + H * Δ * L ^ 2 / η ^ 4) ≤ (n : ℝ) + 1) :
    ∃ radius : ℝ, 0 < radius ∧
      (37 / 400) * (Δ / η) ≤ radius ∧ radius ≤ (37 / 200) * (Δ / η) ∧
      (∀ u ∈ goodHiddenFamily n η H Δ,
        SmoothStochasticClass (gaussianRooms n (calibratedDepth (4 * η) H Δ))
          (familyPopulation η H Δ u) (familySample η H Δ L u)
          (sampleLipschitzModulus (4 * η) L) radius H L Δ) ∧
      (∀ (Seed : Type u) [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
        (N : ℕ) (p : CountableRoomPolicy Seed n)
        (out : LinearHistory Seed N → Space n), Measurable out →
        (∀ u ∈ goodHiddenFamily n η H Δ,
          (1 / 2 : ℝ≥0∞) ≤
            (ν.prod (Measure.infinitePi (fun _ : ℕ => gaussianRooms n (calibratedDepth (4 * η) H Δ))))
            {rz | ‖gradient (familyPopulation η H Δ u)
              (out (sampleTranscript p.point p.handle (familySample η H Δ L) N (u, rz)))‖ ≤ η}) →
        lowerConstant * (((n : ℝ) + 1) * L ^ 2 * H * Δ / η ^ 4) ≤ N) := by
  obtain ⟨radius, hrpos, hrlo, hrhi, hclass, _, _⟩ :=
    bounded_smooth_lower_bound.{u} hη hH hΔ hL hsmall hlarge hd
  refine ⟨radius, hrpos, hrlo, hrhi, hclass, ?_⟩
  intro Seed _ ν _ N p out hout hsuccess
  have hdim := transverse_dimension_of_absolute (show 0 ≤ H * Δ * L ^ 2 / η ^ 4 by positivity) hd
  have hb := countable_smooth_evaluation_lower_bound ν p hdim.1 hη hH hΔ hL
    (depth_regime_of_absolute hlarge) (accuracy_scale_of_absolute hη hsmall) hdim.2 out hout hsuccess
  exact (smooth_coefficient_of_absolute hη hH hΔ).trans hb

theorem goldstein_main_lower_bound {n : ℕ} {ε δ Δ L : ℝ}
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
        (N : ℕ) (p : CountableRoomPolicy Seed n)
        (out : LinearHistory Seed N → Space n), Measurable out →
        (∀ u ∈ goodHiddenFamily n (2 * ε) (ε / δ) Δ,
          (1 / 2 : ℝ≥0∞) ≤
            (ν.prod (Measure.infinitePi
              (fun _ : ℕ => gaussianRooms n (calibratedDepth (4 * (2 * ε)) (ε / δ) Δ))))
            {rz | clarkeGoldsteinResidual (familyPopulation (2 * ε) (ε / δ) Δ u) δ
              (out (sampleTranscript p.point p.handle (familySample (2 * ε) (ε / δ) Δ L) N (u, rz))) ≤ ε}) →
        lowerConstant * (((n : ℝ) + 1) * L ^ 2 * Δ / (δ * ε ^ 3)) ≤ N) := by
  obtain ⟨radius, hrpos, hrlo, hrhi, hclass, _⟩ :=
    bounded_goldstein_lower_bound.{u} hε hδ hΔ hL hsmall hlarge hd
  refine ⟨radius, hrpos, hrlo, hrhi, hclass, ?_⟩
  intro Seed _ ν _ N p out hout hsuccess
  have hdim := goldstein_dimension_of_absolute hε hδ hΔ hd
  have hb := countable_goldstein_evaluation_lower_bound ν p hdim.1 hε hδ hΔ hL
    (goldstein_regime_of_absolute hε hδ hlarge) (goldstein_scale_of_absolute hε hsmall)
    hdim.2 out hout hsuccess
  exact (goldstein_coefficient_of_absolute hε hδ hΔ).trans hb

end NCBall
