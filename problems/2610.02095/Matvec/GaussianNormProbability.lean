import Matvec.GaussianNorm

/-! A dimension-uniform operator-norm cutoff at any requested fixed reliability. -/
namespace Matvec
open MeasureTheory LowRank
noncomputable section

theorem gaussian_norm_reliable_constant (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (iidMatrixLaw (n + 1) (n + 1) 1).real
        {G | C * Real.sqrt (n + 1 : ℝ) < ‖matrixEuclideanMap G‖} ≤ δ := by
  let t := 8 / Real.sqrt δ
  have ht : 0 < t := by dsimp [t]; positivity
  refine ⟨32 + t, by positivity, ?_⟩
  intro n
  let μ := iidMatrixLaw (n + 1) (n + 1) 1
  letI : IsProbabilityMeasure μ := iidMatrixLaw_probability _ _ _
  have hs : 1 ≤ Real.sqrt (n + 1 : ℝ) := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by
      have := Nat.cast_nonneg (α := ℝ) n; nlinarith)
  have hsub : {G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ |
      (32 + t) * Real.sqrt (n + 1 : ℝ) < ‖matrixEuclideanMap G‖} ⊆
      {G | 32 * Real.sqrt (n + 1 : ℝ) + t < ‖matrixEuclideanMap G‖} := by
    intro G hG
    change (32 + t) * Real.sqrt (n + 1 : ℝ) < ‖matrixEuclideanMap G‖ at hG
    change 32 * Real.sqrt (n + 1 : ℝ) + t < ‖matrixEuclideanMap G‖
    nlinarith [mul_le_mul_of_nonneg_left hs ht.le]
  have hbase := gaussian_operator_norm_tail (n + 1) t ht.le
  simp only [Nat.cast_add, Nat.cast_one] at hbase
  have htail := (measureReal_mono (μ := μ) hsub).trans hbase
  apply htail.trans
  have htsq : t ^ 2 / 32 = 2 / δ := by
    dsimp [t]
    rw [div_pow, Real.sq_sqrt hδ.le]
    ring
  have hexp : 2 / δ ≤ Real.exp (t ^ 2 / 32) := by
    have h := Real.add_one_le_exp (t ^ 2 / 32)
    rw [htsq] at h ⊢
    linarith
  rw [show -(t ^ 2) / 32 = -(t ^ 2 / 32) by ring, Real.exp_neg,
    ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  have h := (div_le_iff₀ hδ).mp hexp
  nlinarith

end
end Matvec
