import LowRank.GramSpectrum

/-! Identify the trace deficit with the sum of the largest k squared
eigenvalues minus tr(PH²), as written in the manuscript. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem sum_fin_split_tail {k m : ℕ} (f : Fin (k + m) → ℝ) :
    (∑ i, f i) = (∑ i : Fin m, f (i.castLE (by omega))) +
      ∑ i : Fin k, f ((i.natAdd m).cast (Nat.add_comm m k)) := by
  have h := Fin.sum_univ_add (fun i : Fin (m + k) => f (i.cast (Nat.add_comm m k)))
  rw [Fin.sum_congr' f (Nat.add_comm m k)] at h
  exact h

theorem gramCompressionDeficit_eq_top_sum {d k m : ℕ}
    (H : Matrix (Fin d) (Fin (k + m)) ℝ) (P : Matrix (Fin (k + m)) (Fin (k + m)) ℝ) :
    gramCompressionDeficit H k P =
      (∑ i : Fin k, (orderedMatrixSpectrum (rightGram_posSemidef H).isHermitian).value
        ((i.natAdd m).cast (Nat.add_comm m k))) - (P * (Hᵀ * H)).trace := by
  unfold gramCompressionDeficit
  simp only [Nat.add_sub_cancel_left]
  rw [(orderedMatrixSpectrum (rightGram_posSemidef H).isHermitian).trace]
  simp only [bottomPowerTrace, Real.rpow_one]
  rw [sum_fin_split_tail (k := k) (m := m)
    (orderedMatrixSpectrum (rightGram_posSemidef H).isHermitian).value]
  simp only [add_sub_cancel_left]

theorem gramCompressionDeficit_eq_top_squares {k m : ℕ}
    {H : Matrix (Fin (k + m)) (Fin (k + m)) ℝ} (hH : H.PosSemidef)
    (P : Matrix (Fin (k + m)) (Fin (k + m)) ℝ) :
    gramCompressionDeficit H k P =
      (∑ i : Fin k, (orderedMatrixSpectrum hH.isHermitian).value
        ((i.natAdd m).cast (Nat.add_comm m k)) ^ 2) - (P * (H * H)).trace := by
  rw [gramCompressionDeficit_eq_top_sum, ordered_gram_values_eq_squares hH]
  have hsym : Hᵀ = H := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hH.isHermitian.eq
  rw [hsym]

end
end LowRank
