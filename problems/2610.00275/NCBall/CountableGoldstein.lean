import NCBall.CountableLower
import NCBall.ClarkeLower

/-! # Clarke Goldstein complexity with an unrestricted countable sample pool -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NCBall

def countableClarkeSuccess {S : Type*} [MeasurableSpace S] {n M : ℕ}
    (p : CountableRoomPolicy S n) (ρ η σ δ ε : ℝ) (N : ℕ)
    (out : LinearHistory S N → Space n) : Set (HiddenTable n M × (S × (ℕ → SampleNoise n M))) :=
  {w | clarkeGoldsteinResidual (fixedPopulationValue ρ (4 * η) (calibratedLam (4 * η)) w.1) δ
    (out (sampleTranscript p.point p.handle
      (fixedSampleValue ρ (4 * η) (calibratedLam (4 * η)) σ) N w)) ≤ ε}

theorem countable_clarke_success_subset {S : Type*} [MeasurableSpace S] {n M N : ℕ}
    (p : CountableRoomPolicy S n) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (σ : ℝ)
    (out : LinearHistory S N → Space n) (u : HiddenTable n M)
    (hu : u ∈ fixedGoodEvent (Real.sqrt (n : ℝ))⁻¹) :
    {rz : S × (ℕ → SampleNoise n M) | (u, rz) ∈ countableClarkeSuccess p
      (calibratedRho (4 * (2 * ε)) (ε / δ)) (2 * ε) σ δ ε N out} ⊆
    {rz | (u, rz) ∈ countableGradientSuccess p
      (calibratedRho (4 * (2 * ε)) (ε / δ)) (2 * ε) σ N out} := by
  intro rz hs
  let ρ := calibratedRho (4 * (2 * ε)) (ε / δ)
  let f := fixedPopulationValue ρ (4 * (2 * ε)) (calibratedLam (4 * (2 * ε))) u
  let x := out (sampleTranscript p.point p.handle
    (fixedSampleValue ρ (4 * (2 * ε)) (calibratedLam (4 * (2 * ε))) σ) N (u, rz))
  have hf : ContDiff ℝ 1 f := (chainValue_smooth _ _ _ _ _ _).of_le (by norm_num)
  have hl : LipschitzWith ⟨ε / δ, by positivity⟩ (gradient f) :=
    calibrated_gradient_lipschitz (by positivity) (by positivity) _ (fixedDirections_clock _ u) hu
  change clarkeGoldsteinResidual f δ x ≤ ε at hs
  rw [clarkeGoldsteinResidual_eq_of_C1 hf] at hs
  change ‖gradient f x‖ ≤ 2 * ε
  apply smoothGoldstein_implies_norm_le_two_mul (gradient f) hδ hε.le x _ hs
  intro y _
  simpa only [dist_eq_norm, NNReal.coe_mk] using hl.dist_le_mul y x

theorem countable_goldstein_evaluation_lower_bound {S : Type*} [MeasurableSpace S]
    {n N : ℕ} (ν : Measure S) [IsProbabilityMeasure ν]
    (p : CountableRoomPolicy S n) (hn : 0 < n) {ε δ Δ L : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hΔ : 0 ≤ Δ) (hL : 0 < L)
    (hregime : 200 * bumpConstant * (4 * (2 * ε)) ^ 2 ≤ (ε / δ) * Δ)
    (hscale : (4 * (2 * ε)) * (bumpConstant + 2) ≤ L / 4)
    (hlog : 12800 * Real.log (2 + (ε / δ) * Δ * L ^ 2 / (2 * ε) ^ 4) ≤ n)
    (out : LinearHistory S N → Space n) (hout : Measurable out)
    (hsuccess : ∀ u ∈ fixedGoodEvent (n := n)
      (M := calibratedDepth (4 * (2 * ε)) (ε / δ) Δ) (Real.sqrt (n : ℝ))⁻¹,
      (1 / 2 : ℝ≥0∞) ≤
        (ν.prod (Measure.infinitePi (fun _ : ℕ => gaussianRooms n (calibratedDepth (4 * (2 * ε)) (ε / δ) Δ))))
        {rz | (u, rz) ∈ countableClarkeSuccess p (calibratedRho (4 * (2 * ε)) (ε / δ))
          (2 * ε) (L / (4 * (2 * ε))) δ ε N out}) :
    ((n : ℝ) + 1) * L ^ 2 * Δ / (52428800 * bumpConstant * δ * ε ^ 3) ≤ N := by
  have hg : ∀ u ∈ fixedGoodEvent (n := n)
      (M := calibratedDepth (4 * (2 * ε)) (ε / δ) Δ) (Real.sqrt (n : ℝ))⁻¹,
      (1 / 2 : ℝ≥0∞) ≤
        (ν.prod (Measure.infinitePi (fun _ : ℕ => gaussianRooms n (calibratedDepth (4 * (2 * ε)) (ε / δ) Δ))))
        {rz | (u, rz) ∈ countableGradientSuccess p (calibratedRho (4 * (2 * ε)) (ε / δ))
          (2 * ε) (L / (4 * (2 * ε))) N out} := by
    intro u hu
    exact (hsuccess u hu).trans (measure_mono (countable_clarke_success_subset p hδ hε _ out u hu))
  have hb := countable_smooth_evaluation_lower_bound ν p hn (by positivity : 0 < 2 * ε)
    (by positivity : 0 < ε / δ) hΔ hL hregime hscale hlog out hout hg
  convert hb using 1
  field_simp [ne_of_gt hε, ne_of_gt hδ, ne_of_gt bumpConstant_pos]
  ring

end NCBall
