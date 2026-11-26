import NCBall.ZerothOrderProcess
import NCBall.UpperFirstOrderConfig
import NCBall.UpperSmoothingParameters
import NCBall.NonsmoothZeroGap

/-! # A local stochastic zeroth-order guarantee with fixed algorithm parameters -/

noncomputable section
open MeasureTheory Set Metric
namespace NCBall

def positiveZerothConfig (n : ℕ) (δ Δ L ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεL : ε ≤ L) : UpperConfig :=
  localUpperConfig (Real.sqrt (n + 1 : ℝ) * L) (upperSmoothedGap δ Δ L)
    (upperGoldsteinRadius δ Δ L) ε (upperGoldsteinRadius_pos hδ) hε (upper_variance_scale_ge hε hεL n)

structure ZerothGuarantee {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (f : CoordSpace (n + 1) → ℝ)
    (F : Ξ → CoordSpace (n + 1) → ℝ) (x₀ : CoordSpace (n + 1))
    (δ ε R ρ : ℝ) (hρ : 0 < ρ) (c : UpperConfig) : Prop where
  output_measurable : Measurable (upperRandomOutput c.D c.nonneg c.α (stochasticChord F ρ) x₀ c.m (K := c.K))
  queries_measurable : ∀ t,
    Measurable (fun w => zerothPlusQuery ρ c.D c.nonneg c.α F x₀ w t) ∧
      Measurable (fun w => zerothMinusQuery ρ c.D c.nonneg c.α F x₀ w t)
  queries_inside : ∀ w : UpperRandomness (StochasticChordSeed n Ξ), ∀ t < c.K * c.m,
    zerothPlusQuery ρ c.D c.nonneg c.α F x₀ w t ∈ closedBall x₀ R ∧
      zerothMinusQuery ρ c.D c.nonneg c.α F x₀ w t ∈ closedBall x₀ R
  output_inside : ∀ w : UpperRandomness (StochasticChordSeed n Ξ) × Fin c.K,
    upperRandomOutput c.D c.nonneg c.α (stochasticChord F ρ) x₀ c.m w ∈ closedBall x₀ R
  success_event : ∃ S : Set (UpperRandomness (StochasticChordSeed n Ξ) × Fin c.K), MeasurableSet S ∧
    (1 / 2 : ℝ) ≤ (upperOutputLaw (stochasticChordLaw μ n ρ hρ) c.K c.K_pos).real S ∧
    ∀ w ∈ S, clarkeGoldsteinResidual f δ
      (upperRandomOutput c.D c.nonneg c.α (stochasticChord F ρ) x₀ c.m w) ≤ ε

variable {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
  {f : CoordSpace (n + 1) → ℝ} {F : Ξ → CoordSpace (n + 1) → ℝ} {ℓ : Ξ → ℝ}
  {δ Δ L ε R : ℝ}

theorem positiveZerothConfig_scalar_bound (hδ : 0 < δ) (hΔ : 0 < Δ) (hε : 0 < ε) (hεL : ε ≤ L) :
    let c := positiveZerothConfig n δ Δ L ε hδ hε hεL
    (2 * (c.K * c.m) : ℕ) ≤ 5800 * (1 + (n + 1 : ℝ) * L ^ 2 * Δ / (δ * ε ^ 3)) := by
  apply upper_scalar_call_bound hδ hΔ hε hεL
  exact localUpperConfig_steps _ _ _ _ _ _ _ (upperSmoothedGap_bounds hδ hΔ (hε.trans_le hεL)).1.le

theorem positive_zeroth_guarantee (hs : LipschitzSampleModel μ f F ℓ L)
    (hδ : 0 < δ) (hΔ : 0 < Δ) (hε : 0 < ε) (hεL : ε ≤ L)
    (hR : 11 * Δ / ε ≤ R) (x₀ : CoordSpace (n + 1))
    (hgap : ∀ x ∈ closedBall x₀ R, f x₀ - f x ≤ Δ) :
    ZerothGuarantee μ f F x₀ δ ε R (upperSmoothRadius δ Δ L)
      (upperSmoothRadius_pos hδ hΔ (hε.trans_le hεL)) (positiveZerothConfig n δ Δ L ε hδ hε hεL) := by
  let ρ := upperSmoothRadius δ Δ L
  let ν := upperGoldsteinRadius δ Δ L
  let c := positiveZerothConfig n δ Δ L ε hδ hε hεL
  have hL : 0 < L := hε.trans_le hεL
  have hρ : 0 < ρ := upperSmoothRadius_pos hδ hΔ hL
  have hν : 0 < ν := upperGoldsteinRadius_pos hδ
  have hf := hs.population_lipschitz hL.le
  have hpad : 10 * Δ / ε + ρ ≤ R := upper_radius_padding hΔ hε hεL hR
  have hinner : 0 < 10 * Δ / ε := by positivity
  have hinR : 10 * Δ / ε ≤ R := by linarith
  have hsgap : ∀ x ∈ closedBall x₀ (10 * Δ / ε),
      ballAverage volume ρ hρ f x₀ - ballAverage volume ρ hρ f x ≤ upperSmoothedGap δ Δ L := by
    intro x hx
    have hx' : ‖x - x₀‖ ≤ 10 * Δ / ε := by simpa only [mem_closedBall, dist_eq_norm] using hx
    have hg := ballAverage_local_gap volume ρ hρ hf x₀ hgap (by linarith : ‖x - x₀‖ + ρ ≤ R)
    simpa only [Real.coe_toNNReal _ hL.le, upperSmoothedGap, ρ] using hg
  obtain ⟨hmeas, hcenters, hout, S, hS, hmass, hsuccess⟩ := localUpperConfig_success
    (ballAverage_contDiff volume ρ hρ hf) (stochasticChord_oracle hs hL.le hρ)
    hν hε (upper_variance_scale_ge hε hεL n)
    (upperSmoothedGap_bounds hδ hΔ hL).1.le hinner (upper_smoothed_path_bound hδ hΔ hε hεL) x₀ hsgap
  refine ⟨hmeas, ?_, ?_, ?_, S, hS, hmass, ?_⟩
  · intro t
    exact ⟨zerothPlusQuery_measurable ρ c.D c.nonneg c.α F hs.jointly_measurable x₀ t,
      zerothMinusQuery_measurable ρ c.D c.nonneg c.α F hs.jointly_measurable x₀ t⟩
  · intro w t ht
    have hx : ‖upperLocation c.D c.nonneg c.α (stochasticChord F ρ) x₀ w.1 w.2 t - x₀‖ ≤ 10 * Δ / ε := by
      simpa only [mem_closedBall, dist_eq_norm] using hcenters w t ht
    exact chord_queries_in_padded_ball hρ.le x₀ _ (by linarith) (w.2 t).2
  · intro w
    exact (closedBall_subset_closedBall hinR) (hout w)
  · intro w hw
    have htransfer := ballAverage_residual_bound volume ρ hρ hf hν.le
      (upperRandomOutput c.D c.nonneg c.α (stochasticChord F ρ) x₀ c.m w)
    rw [show ρ + ν = δ from upper_radii_sum δ Δ L] at htransfer
    exact htransfer.trans (hsuccess w hw)

theorem zero_gap_zeroth_guarantee (hs : LipschitzSampleModel μ f F ℓ L)
    (hδ : 0 < δ) (hR : 0 < R) (hε : 0 < ε) (hεL : ε ≤ L) (x₀ : CoordSpace (n + 1))
    (hgap : ∀ x ∈ closedBall x₀ R, f x₀ - f x ≤ 0) :
    ZerothGuarantee μ f F x₀ δ ε R (min δ R / 2)
      (div_pos (lt_min hδ hR) (by norm_num)) trivialUpperConfig := by
  let ρ := min δ R / 2
  have hρ : 0 < ρ := div_pos (lt_min hδ hR) (by norm_num)
  have hρR : ρ ≤ R := by dsimp [ρ]; linarith [min_le_right δ R]
  have hG := stochasticChord_joint_measurable F hs.jointly_measurable ρ
  refine ⟨upperRandomOutput_measurable 0 le_rfl 1 (stochasticChord F ρ) hG x₀ 1 1, ?_, ?_, ?_, ?_⟩
  · intro t
    exact ⟨zerothPlusQuery_measurable ρ 0 le_rfl 1 F hs.jointly_measurable x₀ t,
      zerothMinusQuery_measurable ρ 0 le_rfl 1 F hs.jointly_measurable x₀ t⟩
  · intro w t ht
    have ht0 : t = 0 := by simpa only [trivialUpperConfig, mul_one, Nat.lt_one_iff] using ht
    subst t
    have hp := chord_queries_in_padded_ball hρ.le x₀ x₀ (by simpa using hρR) (w.2 0).2
    simpa only [zerothPlusQuery, zerothMinusQuery, trivialUpperConfig, upperLocation, upperState,
      smul_zero, add_zero] using hp
  · intro w
    simpa only [trivialUpperConfig, upperRandomOutput_one] using mem_closedBall_self hR.le (x := x₀)
  · refine ⟨univ, MeasurableSet.univ, by norm_num, ?_⟩
    intro w _
    simp only [trivialUpperConfig, upperRandomOutput_one]
    exact (zero_gap_lipschitz_start_stationary volume (hs.population_lipschitz (hε.trans_le hεL).le)
      x₀ hδ hR hgap).trans hε.le

end NCBall
