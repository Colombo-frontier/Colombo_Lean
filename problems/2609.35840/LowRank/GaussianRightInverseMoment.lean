import LowRank.GaussianRightInverse

/-! The exact mean squared Frobenius norm of the canonical Gaussian right
inverse, including its orthogonal compression from the algorithm's seed. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators ENNReal
noncomputable section

theorem inverseGram_diagonal_nonneg {d k : ℕ} (X : Matrix (Fin d) (Fin k) ℝ) (i : Fin k) :
    0 ≤ inverseGram X i i := by
  simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using
    (inverseGram_posSemidef X).2 (Pi.single i 1)

theorem iidMatrixLaw_inverseGram_diagonal_mean {d s : ℕ} (hs : s + 3 ≤ d) (i : Fin (s + 1)) :
    (∫⁻ X, ENNReal.ofReal (inverseGram X i i) ∂iidMatrixLaw d (s + 1) 1) =
      ENNReal.ofReal ((((d - s : ℕ) : ℝ) - 2)⁻¹) := by
  have h := iidMatrixLaw_inverseGram_quadratic_moment (by omega : s + 1 ≤ d)
    (by norm_num : (1 : NNReal) ≠ 0) (Pi.single i 1) 1
  rw [reciprocalSquaredGaussianMoment_formula (by omega : 2 * 1 < d - s)] at h
  simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using h

theorem iidMatrixLaw_inverseGram_trace_mean {d k : ℕ} (hk : k + 2 ≤ d) :
    (∫⁻ X, ENNReal.ofReal (inverseGram X).trace ∂iidMatrixLaw d k 1) =
      ENNReal.ofReal ((k : ℝ) / ((d : ℝ) - k - 1)) := by
  cases k with
  | zero => simp [Matrix.trace, Matrix.diag]
  | succ s =>
    have hsum (X : Matrix (Fin d) (Fin (s + 1)) ℝ) :
        ENNReal.ofReal (inverseGram X).trace = ∑ i, ENNReal.ofReal (inverseGram X i i) :=
      ENNReal.ofReal_sum_of_nonneg (fun i _ => inverseGram_diagonal_nonneg X i)
    simp_rw [hsum]
    have hm (i : Fin (s + 1)) : Measurable (fun X : Matrix (Fin d) (Fin (s + 1)) ℝ =>
        ENNReal.ofReal (inverseGram X i i)) :=
      ((measurable_pi_apply i).comp ((measurable_pi_apply i).comp
        (measurable_inverseGram d (s + 1)))).ennreal_ofReal
    rw [lintegral_finset_sum _ (fun i _ => hm i)]
    simp_rw [iidMatrixLaw_inverseGram_diagonal_mean (by omega : s + 3 ≤ d)]
    have hden : (((d - s : ℕ) : ℝ) - 2) = (d : ℝ) - (s + 1 : ℕ) - 1 := by
      rw [Nat.cast_sub (by omega : s ≤ d)]
      push_cast
      ring
    rw [hden]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ s + 1)]
    simp only [div_eq_mul_inv, Nat.cast_add, Nat.cast_one]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by
      have hd : (s : ℝ) + 1 + 2 ≤ d := by exact_mod_cast hk
      linarith)]

theorem iidMatrixLaw_gramRightInverse_mean {k s : ℕ} (hs : k + 2 ≤ s) :
    (∫⁻ G, ENNReal.ofReal (frobeniusSq (gramRightInverse G)) ∂iidMatrixLaw k s 1) =
      ENNReal.ofReal ((k : ℝ) / ((s : ℝ) - k - 1)) := by
  simp_rw [frobeniusSq_gramRightInverse]
  have hf : Measurable (fun X : Matrix (Fin s) (Fin k) ℝ => ENNReal.ofReal (inverseGram X).trace) := by
    have hm := measurable_inverseGram s k
    simp only [Matrix.trace, Matrix.diag]
    fun_prop
  rw [← lintegral_map hf (iidMatrixLaw_transpose_preserving k s 1).measurable,
    (iidMatrixLaw_transpose_preserving k s 1).map_eq,
    iidMatrixLaw_inverseGram_trace_mean hs]

theorem iidMatrixLaw_compressed_gramRightInverse_mean {d k s : ℕ}
    (V : Matrix (Fin d) (Fin k) ℝ) (hV : Vᵀ * V = 1) (hs : k + 2 ≤ s) :
    (∫⁻ U, ENNReal.ofReal (frobeniusSq (gramRightInverse (Vᵀ * U))) ∂iidMatrixLaw d s 1) =
      ENNReal.ofReal ((k : ℝ) / ((s : ℝ) - k - 1)) := by
  have hf : Measurable (fun G : Matrix (Fin k) (Fin s) ℝ =>
      ENNReal.ofReal (frobeniusSq (gramRightInverse G))) := by
    have hm := measurable_gramRightInverse k s
    unfold frobeniusSq
    fun_prop
  rw [← lintegral_map hf (iidMatrixLaw_left_compression_preserving V hV 1).measurable,
    iidMatrixLaw_left_compression V hV, iidMatrixLaw_gramRightInverse_mean hs]

end
end LowRank
