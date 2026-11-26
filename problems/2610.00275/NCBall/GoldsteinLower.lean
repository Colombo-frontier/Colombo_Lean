import NCBall.SmoothLower
import NCBall.BoundedRadius
import NCBall.Goldstein

/-! # The smooth Goldstein product lower bound for the constructed family -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NCBall

def fullGoldsteinSuccess {R : Type*} [MeasurableSpace R] {n K M : ℕ}
    (p : RoomQueryPolicy R n K) (ρ η σ scale δ ε : ℝ)
    (N : ℕ) (out : LinearHistory R N → Space n) : Set (R × RoomLatents n K M) :=
  {w | smoothGoldsteinResidual
    (gradient (fullPopulation ρ (4 * η) (calibratedLam (4 * η)) scale w.2)) δ
    (out (oracleTranscript (fullRealReply p ρ (4 * η) (calibratedLam (4 * η)) σ scale) N w)) ≤ ε}

theorem fixed_goldstein_success_subset {R : Type*} [MeasurableSpace R] {n K M N : ℕ}
    (p : RoomQueryPolicy R n K) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (σ scale : ℝ)
    (out : LinearHistory R N → Space n) (u : HiddenTable n M) (hu : u ∈ fixedGoodEvent scale) :
    {rz : R × SampleTable n K M | experimentFromSplit (u, rz) ∈
      fullGoldsteinSuccess p (calibratedRho (4 * (2 * ε)) (ε / δ)) (2 * ε) σ scale δ ε N out} ⊆
    {rz | experimentFromSplit (u, rz) ∈
      fullGradientSuccess p (calibratedRho (4 * (2 * ε)) (ε / δ)) (2 * ε) σ scale N out} := by
  intro rz hs
  let w := experimentFromSplit (u, rz)
  let ρ := calibratedRho (4 * (2 * ε)) (ε / δ)
  let f := fullPopulation ρ (4 * (2 * ε)) (calibratedLam (4 * (2 * ε))) scale w.2
  let x := out (oracleTranscript (fullRealReply p ρ (4 * (2 * ε))
    (calibratedLam (4 * (2 * ε))) σ scale) N w)
  have hf : f = chainValue M ρ (4 * (2 * ε)) (calibratedLam (4 * (2 * ε)))
      (roomCenter ρ (fixedDirections scale u)) (fixedDirections scale u) := by
    simp only [f, fullPopulation, fullRoomCenters, w, experimentFromSplit, combined_latentDirections]
  have hl : LipschitzWith ⟨ε / δ, by positivity⟩ (gradient f) := by
    rw [hf]
    exact calibrated_gradient_lipschitz (by positivity) (by positivity) (fixedDirections scale u)
      (fixedDirections_clock scale u) hu
  change smoothGoldsteinResidual (gradient f) δ x ≤ ε at hs
  change ‖gradient f x‖ ≤ 2 * ε
  apply smoothGoldstein_implies_norm_le_two_mul (gradient f) hδ hε.le x _ hs
  intro y _
  simpa only [dist_eq_norm, NNReal.coe_mk] using hl.dist_le_mul y x

theorem goldstein_scalar_evaluation_lower_bound {R : Type*} [MeasurableSpace R]
    {n K N : ℕ} (ν : Measure R) [IsProbabilityMeasure ν]
    (p : RoomQueryPolicy R n K) (hn : 0 < n) {ε δ Δ L : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hΔ : 0 ≤ Δ) (hL : 0 < L)
    (hregime : 200 * bumpConstant * (4 * (2 * ε)) ^ 2 ≤ (ε / δ) * Δ)
    (hscale : (4 * (2 * ε)) * (bumpConstant + 2) ≤ L / 4)
    (hlog : 12800 * Real.log (2 + (ε / δ) * Δ * L ^ 2 / (2 * ε) ^ 4) ≤ n)
    (out : LinearHistory R N → Space n) (hout : Measurable out)
    (hsuccess : ∀ u ∈ fixedGoodEvent (n := n)
      (M := calibratedDepth (4 * (2 * ε)) (ε / δ) Δ) (Real.sqrt (n : ℝ))⁻¹,
      (1 / 2 : ℝ≥0∞) ≤ (ν.prod (sampleTableLaw n K (calibratedDepth (4 * (2 * ε)) (ε / δ) Δ)))
        {rz | experimentFromSplit (u, rz) ∈ fullGoldsteinSuccess p
          (calibratedRho (4 * (2 * ε)) (ε / δ)) (2 * ε) (L / (4 * (2 * ε)))
          (Real.sqrt (n : ℝ))⁻¹ δ ε N out}) :
    ((n : ℝ) + 1) * L ^ 2 * Δ / (52428800 * bumpConstant * δ * ε ^ 3) ≤ N := by
  have hg : ∀ u ∈ fixedGoodEvent (n := n)
      (M := calibratedDepth (4 * (2 * ε)) (ε / δ) Δ) (Real.sqrt (n : ℝ))⁻¹,
      (1 / 2 : ℝ≥0∞) ≤ (ν.prod (sampleTableLaw n K (calibratedDepth (4 * (2 * ε)) (ε / δ) Δ)))
        {rz | experimentFromSplit (u, rz) ∈ fullGradientSuccess p
          (calibratedRho (4 * (2 * ε)) (ε / δ)) (2 * ε) (L / (4 * (2 * ε)))
          (Real.sqrt (n : ℝ))⁻¹ N out} := by
    intro u hu
    exact (hsuccess u hu).trans (measure_mono
      (fixed_goldstein_success_subset p hδ hε _ _ out u hu))
  have hb := smooth_scalar_evaluation_lower_bound ν p hn (by positivity : 0 < 2 * ε)
    (by positivity : 0 < ε / δ) hΔ hL hregime hscale hlog out hout hg
  convert hb using 1
  field_simp [ne_of_gt hε, ne_of_gt hδ, ne_of_gt bumpConstant_pos]
  ring

end NCBall
