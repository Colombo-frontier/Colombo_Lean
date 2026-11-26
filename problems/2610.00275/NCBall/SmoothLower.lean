import NCBall.FixedHardInstance
import NCBall.UniformDimension

/-! # The product lower bound for measurable finite-pool reusable-handle policies

All replies in the success premise are evaluations of the constructed sample
functions. The hard instance is fixed before drawing the seed or sample table.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NCBall

theorem smooth_scalar_evaluation_lower_bound {R : Type*} [MeasurableSpace R]
    {n K N : ℕ} (ν : Measure R) [IsProbabilityMeasure ν]
    (p : RoomQueryPolicy R n K) (hn : 0 < n) {η H Δ L : ℝ}
    (hη : 0 < η) (hH : 0 < H) (hΔ : 0 ≤ Δ) (hL : 0 < L)
    (hregime : 200 * bumpConstant * (4 * η) ^ 2 ≤ H * Δ)
    (hscale : (4 * η) * (bumpConstant + 2) ≤ L / 4)
    (hlog : 12800 * Real.log (2 + H * Δ * L ^ 2 / η ^ 4) ≤ n)
    (out : LinearHistory R N → Space n) (hout : Measurable out)
    (hsuccess : ∀ u ∈ fixedGoodEvent (n := n)
      (M := calibratedDepth (4 * η) H Δ) (Real.sqrt (n : ℝ))⁻¹,
      (1 / 2 : ℝ≥0∞) ≤ (ν.prod (sampleTableLaw n K (calibratedDepth (4 * η) H Δ)))
        {rz | experimentFromSplit (u, rz) ∈ fullGradientSuccess p (calibratedRho (4 * η) H)
          η (L / (4 * η)) (Real.sqrt (n : ℝ))⁻¹ N out}) :
    ((n : ℝ) + 1) * L ^ 2 * H * Δ / (3276800 * bumpConstant * η ^ 4) ≤ N := by
  have hγ : 0 < 4 * η := by positivity
  have hq := calibratedCharges_pos hn hγ hscale
  have hdim := calibrated_dimension_condition hη hH hΔ hlog
  have hgood := dimension_good_log hq hdim
  have hbudget : calibratedDepth (4 * η) H Δ * calibratedCharges n (4 * η) L ≤ N := by
    by_contra h
    have hN : N < calibratedDepth (4 * η) H Δ * calibratedCharges n (4 * η) L := by omega
    obtain ⟨u, hu, hb⟩ := exists_fixed_hard_gradient ν p hq hN hn
      (calibratedRho_pos hγ hH) (by positivity : 0 < L / (4 * η)) hη
      (calibratedCharges_cap n (4 * η) L) hdim hgood out hout
    exact (not_lt_of_ge (hsuccess u hu)) hb
  exact (calibrated_smooth_complexity_lower hn hη hH hΔ hregime hscale).trans
    (by exact_mod_cast hbudget)

end NCBall
