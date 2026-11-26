import MatchingBounds1005.PairTensorEnergy
import MatchingBounds1005.VisibleReadouts

/-! The actual unrevealed signal is a sum of fixed rank-one tensors stopped
once at the deterministic direct-disclosure calendar. -/
noncomputable section
open scoped BigOperators

namespace MatchingBounds1005.TensorGeometry
open TensorChannelRows GaussianBlockProjection

theorem signal_sub_visibleAt {d N k : ℕ} (hk : 1 ≤ k) (w : ℝ)
    (disclose : Fin N → ℕ) (b : Fin N → Vec d) (U : Vec d →L[ℝ] Vec d) (t : ℕ) :
    signal k w (fun i => U (b i)) - signal k w (VisibleReadouts.visibleAt disclose b U t) =
      w • ∑ i, if t < disclose i then rankOne k (U (b i)) else 0 := by
  rw [VisibleReadouts.signal_visibleAt hk]
  unfold signal
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : disclose i ≤ t
  · simp only [if_pos hi, if_neg (Nat.not_lt.mpr hi), sub_self]
  · simp only [if_neg hi, if_pos (Nat.lt_of_not_ge hi), sub_zero]

theorem hidden_coordinates_from_visible {d N k : ℕ} (hk : 1 ≤ k) (w : ℝ)
    (disclose : Fin N → ℕ) (b : Fin N → Vec d) (U : Vec d →L[ℝ] Vec d) (n : ℕ) :
    tensorCoordinates d k (signal k w (fun i => U (b i))) -
      tensorCoordinates d k (signal k w (VisibleReadouts.visibleAt disclose b U (n + 1))) =
      stoppedCoordinates k Finset.univ (fun i => U (b i)) w (fun i => disclose i - 1) n := by
  rw [← map_sub, signal_sub_visibleAt hk, map_smul]
  unfold stoppedCoordinates
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : n + 1 < disclose i ↔ n < disclose i - 1 := by omega
  by_cases hi : n < disclose i - 1
  · rw [if_pos (he.mpr hi), if_pos hi]
  · rw [if_neg (mt he.mp hi), if_neg hi, map_zero]

theorem normalizedSignal_sub {d : ℕ} (σ₃ σ₄ : ℝ)
    (S₃ T₃ : Vec (cubicDim d)) (S₄ T₄ : Vec (quarticDim d)) :
    normalizedSignal σ₃ σ₄ S₃ S₄ - normalizedSignal σ₃ σ₄ T₃ T₄ =
      normalizedSignal σ₃ σ₄ (S₃ - T₃) (S₄ - T₄) := by
  apply (splitLinearEquiv (cubicDim d) (quarticDim d)).injective
  simp only [map_sub, normalizedSignal, LinearEquiv.apply_symm_apply]
  ext <;> simp only [Prod.fst_sub, Prod.snd_sub, smul_sub]

theorem hidden_normalized_signal {d N : ℕ} (σ₃ σ₄ w₃ w₄ : ℝ)
    (disclose : Fin N → ℕ) (b : Fin N → Vec d) (U : Vec d →L[ℝ] Vec d) (n : ℕ) :
    normalizedSignal σ₃ σ₄
        (tensorCoordinates d 3 (signal 3 w₃ (fun i => U (b i))))
        (tensorCoordinates d 4 (signal 4 w₄ (fun i => U (b i)))) -
      normalizedSignal σ₃ σ₄
        (tensorCoordinates d 3 (signal 3 w₃ (VisibleReadouts.visibleAt disclose b U (n + 1))))
        (tensorCoordinates d 4 (signal 4 w₄ (VisibleReadouts.visibleAt disclose b U (n + 1)))) =
      normalizedSignal σ₃ σ₄
        (stoppedCoordinates 3 Finset.univ (fun i => U (b i)) w₃ (fun i => disclose i - 1) n)
        (stoppedCoordinates 4 Finset.univ (fun i => U (b i)) w₄ (fun i => disclose i - 1) n) := by
  rw [normalizedSignal_sub, hidden_coordinates_from_visible (by norm_num : 1 ≤ 3),
    hidden_coordinates_from_visible (by norm_num : 1 ≤ 4)]

theorem stoppedCoordinates_truncate {ι : Type*} {d : ℕ} (k : ℕ) (signals : Finset ι)
    (b : ι → Vec d) (w : ℝ) (ell : ι → ℕ) {n T : ℕ} (hn : n < T) :
    stoppedCoordinates k signals b w (fun i => min (ell i) T) n =
      stoppedCoordinates k signals b w ell n := by
  unfold stoppedCoordinates
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [lt_min_iff, hn, and_true]

end MatchingBounds1005.TensorGeometry
