import FreshGradientMinimax.RobinMultiSmooth

/-! The global quadratic growth bound for the original multi-chain energy. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

theorem clip_two_coordinate {m : ℕ} (u : Euclid m) (i : Fin m) : |clipVector 2 u i| ≤ 3 := by
  simpa only [clipVector_apply, show 3 * (2 : ℝ) / 2 = 3 by norm_num] using
    smoothClip_bound (by norm_num : (0 : ℝ) < 2) (u i)

theorem clip_two_norm_sq {m : ℕ} (u : Euclid m) : ‖clipVector 2 u‖ ^ 2 ≤ 9 * m := by
  rw [euclid_norm_sq]
  calc
    _ ≤ ∑ _ : Fin m, (9 : ℝ) := Finset.sum_le_sum (fun i _ => by
      have h := pow_le_pow_left₀ (abs_nonneg _) (clip_two_coordinate u i) 2
      simpa only [sq_abs, show (3 : ℝ) ^ 2 = 9 by norm_num] using h)
    _ = _ := by simp [mul_comm]

theorem robinPrimalMap_norm_sq_bound {n : ℕ} (hn : 10 ≤ n + 2) (k : ℕ) (q : Euclid (k * 2 + 1)) :
    ‖robinPrimalMap n k q‖ ^ 2 ≤ 84 * ‖q‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) ((robinPrimalMap n k).le_opNorm q) 2
  rw [mul_pow] at h
  exact h.trans (mul_le_mul_of_nonneg_right (robinPrimalMap_opNorm_sq hn k) (sq_nonneg _))

theorem robinMultiEnergy_bounds {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    0 ≤ robinMultiEnergy n k δ u y ∧
      robinMultiEnergy n k δ u y ≤ 2000 * (k + 1 : ℕ) + 5 * ‖y‖ ^ 2 := by
  have hQ := boundedEnergy_bounds hδ (by norm_num : (0 : ℝ) ≤ 1000) (robinBlockEdges n k (clipVector 2 u) y)
  refine ⟨hQ.1, ?_⟩
  have hsum := norm_add_sq_le_two (robinDualMap n k y) (robinPrimalMap n k (clipVector 2 u))
  have hY := pow_le_pow_left₀ (norm_nonneg _) (robinDualMap_norm n k y) 2
  have hX := robinPrimalMap_norm_sq_bound hn k (clipVector 2 u)
  have hclip := clip_two_norm_sq u
  have hQ2 := hQ.2
  change robinMultiEnergy n k δ u y ≤ ‖robinDualMap n k y + robinPrimalMap n k (clipVector 2 u)‖ ^ 2 / 2 at hQ2
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at *
  nlinarith only [hQ2, hsum, hY, hX, hclip, sq_nonneg ‖y‖, Nat.cast_nonneg (α := ℝ) k]

theorem boundedEnergy_blocks {k m : ℕ} (δ b : ℝ) (x : Euclid (k * m)) :
    boundedEnergy δ b x = ∑ i : Fin k, boundedEnergy δ b (euclidBlock i x) := by
  unfold boundedEnergy
  rw [sum_fin_blocks]
  rfl

theorem robinMultiEnergy_blocks (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    robinMultiEnergy n k δ u y = ∑ i : Fin k,
      affineBoundedEnergy (robinIncidence (n + 2))
        (robinEdgeShift n (clipVector 2 u (interleavedX i)) (clipVector 2 u (interleavedZ i) / 2))
        δ 1000 (euclidBlock i y) := by
  rw [robinMultiEnergy, boundedEnergy_blocks]
  simp only [robinBlockEdges_block, affineBoundedEnergy]

end FreshGradientMinimax
