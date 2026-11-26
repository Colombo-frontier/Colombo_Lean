import NCBall.BallRegularity
import NCBall.LocalGoldsteinGap

/-! # A local minimum of a Lipschitz function is Goldstein stationary

Positive smoothing radii tend to zero through an explicit epsilon
argument. The query ball and Goldstein radius need only be positive.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped NNReal
namespace NCBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem clarkeGoldsteinSet_radius_mono (f : E → ℝ) (x : E) {ρ ν : ℝ} (h : ρ ≤ ν) :
    clarkeGoldsteinSet f ρ x ⊆ clarkeGoldsteinSet f ν x := by
  apply (closedConvexHull ℝ).monotone
  rintro v ⟨y, hy, hv⟩
  exact ⟨y, (closedBall_subset_closedBall h) hy, hv⟩

theorem clarkeGoldsteinSet_nonempty_of_lipschitz (τ : Measure E) [τ.IsAddHaarMeasure]
    {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) {ρ : ℝ} (hρ : 0 < ρ) (x : E) :
    (clarkeGoldsteinSet f ρ x).Nonempty :=
  ⟨gradient (ballAverage τ ρ hρ f) x, ballAverage_gradient_mem τ ρ hρ hf x⟩

theorem clarkeGoldsteinResidual_radius_antitone_lipschitz (τ : Measure E) [τ.IsAddHaarMeasure]
    {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (x : E) {ρ ν : ℝ}
    (hρ : 0 < ρ) (hρν : ρ ≤ ν) :
    clarkeGoldsteinResidual f ν x ≤ clarkeGoldsteinResidual f ρ x :=
  infDist_le_infDist_of_subset (clarkeGoldsteinSet_radius_mono f x hρν)
    (clarkeGoldsteinSet_nonempty_of_lipschitz τ hf hρ x)

theorem zero_gap_lipschitz_start_stationary (τ : Measure E) [τ.IsAddHaarMeasure]
    {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (x₀ : E) {δ R : ℝ}
    (hδ : 0 < δ) (hR : 0 < R) (hgap : ∀ x ∈ closedBall x₀ R, f x₀ - f x ≤ 0) :
    clarkeGoldsteinResidual f δ x₀ ≤ 0 := by
  suffices heps : ∀ ε : ℝ, 0 < ε → clarkeGoldsteinResidual f δ x₀ ≤ ε by
    by_contra! hpos
    have hh := heps (clarkeGoldsteinResidual f δ x₀ / 2) (by linarith)
    linarith
  intro ε hε
  let ν := min δ R / 2
  have hν : 0 < ν := div_pos (lt_min hδ hR) (by norm_num)
  have hνδ : 2 * ν ≤ δ := by dsimp [ν]; linarith [min_le_left δ R]
  have hνR : 2 * ν ≤ R := by dsimp [ν]; linarith [min_le_right δ R]
  let ρ := min ν (ε * ν / ((L : ℝ) + 1))
  have hL1 : 0 < (L : ℝ) + 1 := by positivity
  have hρ : 0 < ρ := lt_min hν (div_pos (mul_pos hε hν) hL1)
  have hρν : ρ ≤ ν := min_le_left _ _
  have hρε : ρ * ((L : ℝ) + 1) ≤ ε * ν :=
    (le_div_iff₀ hL1).mp (min_le_right _ _)
  have hsumδ : ρ + ν ≤ δ := by linarith
  have hsumR : ρ + ν ≤ R := by linarith
  have hsgap : ∀ x ∈ closedBall x₀ ν,
      ballAverage τ ρ hρ f x₀ - ballAverage τ ρ hρ f x ≤ (L : ℝ) * ρ := by
    intro x hx
    have hx' : ‖x - x₀‖ ≤ ν := by simpa only [mem_closedBall, dist_eq_norm] using hx
    simpa only [zero_add] using ballAverage_local_gap τ ρ hρ hf x₀ hgap (by linarith : ‖x - x₀‖ + ρ ≤ R)
  calc
    _ ≤ clarkeGoldsteinResidual f (ρ + ν) x₀ :=
      clarkeGoldsteinResidual_radius_antitone_lipschitz τ hf x₀ (add_pos hρ hν) hsumδ
    _ ≤ clarkeGoldsteinResidual (ballAverage τ ρ hρ f) ν x₀ :=
      ballAverage_residual_bound τ ρ hρ hf hν.le x₀
    _ ≤ ((L : ℝ) * ρ) / ν :=
      clarkeGoldsteinResidual_le_local_gap (ballAverage_contDiff τ ρ hρ hf) x₀ hν le_rfl le_rfl hsgap
    _ ≤ ε := (div_le_iff₀ hν).mpr (by nlinarith)

end NCBall
