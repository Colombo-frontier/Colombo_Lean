import NCBall.VerifiedFamily
import Mathlib.Analysis.Convex.Extrema

/-! # The constructed functions are nonconvex even on their query ball -/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Topology
namespace NCBall

theorem chainValue_not_convexOn_ball {n M : ℕ} (hM : 1 ≤ M)
    {ρ γ lam : ℝ} (hρ : 0 < ρ) (hγ : 0 < γ)
    (U V : ℕ → Space n) (hU : ∀ i, U i 0 = 0) (hgood : ∀ i < M, ‖U i‖ ≤ 2) :
    ¬ConvexOn ℝ (closedBall (0 : Space n) (37 * M * ρ))
      (chainValue M ρ γ lam (roomCenter ρ U) V) := by
  let f := chainValue M ρ γ lam (roomCenter ρ U) V
  let c := roomCenter ρ U M
  let x : Space n := ((5 * (M : ℝ) + 1) * ρ) • EuclideanSpace.single 0 1
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hxclock : x 0 = (5 * (M : ℝ) + 1) * ρ := by
    simp [x, EuclideanSpace.single_apply]
  have hxnorm : ‖x‖ = (5 * (M : ℝ) + 1) * ρ := by
    simp only [x, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (5 * (M : ℝ) + 1) * ρ),
      EuclideanSpace.norm_single, abs_one, mul_one]
  have hxball : x ∈ closedBall (0 : Space n) (37 * M * ρ) := by
    rw [mem_closedBall, dist_zero_right, hxnorm]
    nlinarith [mul_nonneg (by linarith : 0 ≤ (M : ℝ) - 1) hρ.le]
  have hcout : c ∈ closedBall (0 : Space n) (37 * M * ρ) :=
    all_rooms_in_query_ball hρ.le hM U hgood le_rfl (mem_closedBall_self hρ.le)
  have hcval : f c = -γ * c 0 := chainValue_terminal_core hρ U V hU c (by
    simp only [c, dist_self]
    positivity)
  have hlocal : IsLocalMin f c := by
    change ∀ᶠ y in 𝓝 c, f c ≤ f y
    filter_upwards [ball_mem_nhds c (by positivity : 0 < ρ / 4)] with y hy
    rw [hcval]
    exact le_of_eq (chainValue_terminal_core hρ U V hU y (le_of_lt hy)).symm
  have hxval : f x = -γ * x 0 := by
    apply chainValue_outside hρ
    intro j hj
    have hj' : (j : ℝ) ≤ M := by exact_mod_cast hj
    have hc := (le_abs_self (x 0 - roomCenter ρ U j 0)).trans (clock_dist_le x (roomCenter ρ U j))
    rw [hxclock, roomCenter_clock ρ U hU] at hc
    nlinarith [mul_nonneg (sub_nonneg.mpr hj') hρ.le]
  have hclock : c 0 < x 0 := by
    rw [hxclock, show c 0 = 4 * ρ * M from roomCenter_clock ρ U hU M]
    nlinarith [mul_pos (show (0 : ℝ) < M by linarith) hρ]
  intro hconv
  have hmin := IsMinOn.of_isLocalMinOn_of_convexOn hcout (hlocal.on _) hconv hxball
  change f c ≤ f x at hmin
  rw [hcval, hxval] at hmin
  exact (not_le_of_gt (mul_lt_mul_of_neg_left hclock (by linarith : -γ < 0))) hmin

theorem family_not_convexOn_ball {n : ℕ} {η H Δ : ℝ}
    (hη : 0 < η) (hH : 0 < H)
    (hlarge : regimeConstant * η ^ 2 ≤ H * Δ)
    (u : HiddenTable n (calibratedDepth (4 * η) H Δ))
    (hu : u ∈ goodHiddenFamily n η H Δ) :
    ¬ConvexOn ℝ (closedBall (0 : Space n) (calibratedRadius η H Δ)) (familyPopulation η H Δ u) := by
  have hγ : 0 < 4 * η := by positivity
  have hM := calibratedDepth_ge_two hγ (depth_regime_of_absolute hlarge)
  exact chainValue_not_convexOn_ball (by omega) (calibratedRho_pos hγ hH) hγ _ _
    (fixedDirections_clock _ u) hu

end NCBall
