import FreshGradientMinimax.AcceleratedNonlinearGradient
import FreshGradientMinimax.AcceleratedPenaltyGradient

/-! Actual primal derivatives of D_delta, including clipping and uniform
dimension-independent smoothness and threshold perturbation estimates. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

def acceleratedPrimalPullback (n k : ℕ) (δ : ℝ) (q : Euclid (k * 2 + 1)) : Euclid (k * 2 + 1) :=
  acceleratedNonlinearGradient q + acceleratedPenaltyGradient n k δ q

def acceleratedPrimalGradient (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) : Euclid (k * 2 + 1) :=
  weightedClipGradient 2 (acceleratedPrimalPullback n k δ (clipVector 2 u)) u

theorem acceleratedPrimalPullback_hasFDerivAt (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (q : Euclid (k * 2 + 1)) :
    HasFDerivAt (fun p => acceleratedNonlinear p + acceleratedPenalty n k δ p)
      (innerSL ℝ (acceleratedPrimalPullback n k δ q)) q := by
  have h := (acceleratedNonlinear_hasFDerivAt q).add (acceleratedPenalty_hasFDerivAt n k hδ q)
  apply h.congr_fderiv
  ext v
  simp [acceleratedPrimalPullback, innerSL_apply, inner_add_left]

theorem acceleratedPrimal_hasFDerivAt (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) :
    HasFDerivAt (acceleratedPrimal n k δ) (innerSL ℝ (acceleratedPrimalGradient n k δ u)) u := by
  have h := clipped_scalar_hasFDerivAt (by norm_num : (0 : ℝ) < 2) u
    (acceleratedPrimalPullback n k δ (clipVector 2 u))
    (acceleratedPrimalPullback_hasFDerivAt n k hδ (clipVector 2 u))
  have he : acceleratedPrimal n k δ = fun v =>
      acceleratedNonlinear (clipVector 2 v) + acceleratedPenalty n k δ (clipVector 2 v) :=
    funext (acceleratedPrimal_penalty n k δ)
  rw [he]
  exact h

theorem acceleratedPrimal_gradient (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (u : Euclid (k * 2 + 1)) :
    gradient (acceleratedPrimal n k δ) u = acceleratedPrimalGradient n k δ u :=
  (hasGradientAt_iff_hasFDerivAt.mpr (acceleratedPrimal_hasFDerivAt n k hδ u)).gradient

theorem acceleratedPrimalPullback_coordinate {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (j : Fin (k * 2 + 1)) :
    |acceleratedPrimalPullback n k δ (clipVector 2 u) j| ≤ 348 := by
  have h := abs_add_le (acceleratedNonlinearGradient (clipVector 2 u) j)
    (acceleratedPenaltyGradient n k δ (clipVector 2 u) j)
  have hN := acceleratedNonlinearGradient_coordinate (clipVector 2 u) j
  have hP := acceleratedPenaltyGradient_coordinate hn hδ (clipVector 2 u) j
  have hc := clip_two_coordinate u j
  change |acceleratedPrimalPullback n k δ (clipVector 2 u) j| ≤ _ at h
  linarith only [h, hN, hP, hc]

theorem accelerated_clip_norm {k : ℕ} (u : Euclid (k * 2 + 1)) :
    ‖clipVector 2 u‖ ≤ 6 * Real.sqrt (k + 1 : ℕ) := by
  have h := clip_two_norm_sq u
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg (k + 1))]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h ⊢
  nlinarith only [h, Nat.cast_nonneg (α := ℝ) k]

theorem acceleratedPrimalGradient_norm {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) : ‖acceleratedPrimalGradient n k δ u‖ ≤ 1000 * Real.sqrt (k + 1 : ℕ) := by
  have hclip := weightedClipGradient_norm 2 (acceleratedPrimalPullback n k δ (clipVector 2 u)) u
  have h := norm_add_le (acceleratedNonlinearGradient (clipVector 2 u))
    (acceleratedPenaltyGradient n k δ (clipVector 2 u))
  change ‖acceleratedPrimalPullback n k δ (clipVector 2 u)‖ ≤ _ at h
  change ‖acceleratedPrimalGradient n k δ u‖ ≤ _ at hclip
  have hN := acceleratedNonlinearGradient_norm (clipVector 2 u)
  have hP := acceleratedPenaltyGradient_norm hn hδ (clipVector 2 u)
  have hc := accelerated_clip_norm u
  linarith only [hclip, h, hN, hP, hc, Real.sqrt_nonneg (k + 1 : ℕ)]

theorem acceleratedPrimalPullback_difference {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (q p : Euclid (k * 2 + 1)) :
    ‖acceleratedPrimalPullback n k δ q - acceleratedPrimalPullback n k δ p‖ ≤ 3285 * ‖q - p‖ := by
  have h := norm_add_le (acceleratedNonlinearGradient q - acceleratedNonlinearGradient p)
    (acceleratedPenaltyGradient n k δ q - acceleratedPenaltyGradient n k δ p)
  have he : acceleratedPrimalPullback n k δ q - acceleratedPrimalPullback n k δ p =
      (acceleratedNonlinearGradient q - acceleratedNonlinearGradient p) +
        (acceleratedPenaltyGradient n k δ q - acceleratedPenaltyGradient n k δ p) := by
    unfold acceleratedPrimalPullback
    abel
  rw [he]
  linarith only [h, acceleratedNonlinearGradient_difference q p,
    acceleratedPenaltyGradient_difference hn hδ q p]

theorem acceleratedPrimalGradient_difference {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u v : Euclid (k * 2 + 1)) :
    ‖acceleratedPrimalGradient n k δ u - acceleratedPrimalGradient n k δ v‖ ≤ 4000 * ‖u - v‖ := by
  have h := weightedClipGradient_two_changes (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) ≤ 348) (acceleratedPrimalPullback n k δ (clipVector 2 u))
    (acceleratedPrimalPullback n k δ (clipVector 2 v)) u v
    (acceleratedPrimalPullback_coordinate hn hδ v)
  have hp := acceleratedPrimalPullback_difference hn hδ (clipVector 2 u) (clipVector 2 v)
  have hc := clipVector_sub_norm (by norm_num : (0 : ℝ) < 2) u v
  change ‖acceleratedPrimalGradient n k δ u - acceleratedPrimalGradient n k δ v‖ ≤ _ at h
  norm_num only at h
  linarith only [h, hp, hc, norm_nonneg (u - v)]

theorem acceleratedPrimalGradient_perturbation {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) :
    ‖acceleratedPrimalGradient n k δ u - acceleratedPrimalGradient n k 0 u‖ ≤
      84 * δ * Real.sqrt (k * 2 : ℕ) := by
  have h := weightedClipGradient_sub_weights 2 (acceleratedPrimalPullback n k δ (clipVector 2 u))
    (acceleratedPrimalPullback n k 0 (clipVector 2 u)) u
  have he : acceleratedPrimalPullback n k δ (clipVector 2 u) - acceleratedPrimalPullback n k 0 (clipVector 2 u) =
      acceleratedPenaltyGradient n k δ (clipVector 2 u) - acceleratedPenaltyGradient n k 0 (clipVector 2 u) := by
    unfold acceleratedPrimalPullback
    abel
  rw [he] at h
  exact h.trans (acceleratedPenaltyGradient_perturbation hn hδ (clipVector 2 u))

end FreshGradientMinimax
