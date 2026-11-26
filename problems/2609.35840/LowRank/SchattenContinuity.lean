import LowRank.OrderedSpectrumContinuity

/-! Continuity of the actual Gram singular values, positive-p Schatten
expressions, and the attained rank-k optimal residual. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem continuous_rightGram (d t : ℕ) :
    Continuous (fun X : Matrix (Fin d) (Fin t) ℝ => Xᵀ * X) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  fun_prop

theorem continuous_gram_eigenvalue (d t : ℕ) (i : Fin t) :
    Continuous (fun X : Matrix (Fin d) (Fin t) ℝ =>
      (orderedMatrixSpectrum (rightGram_posSemidef X).isHermitian).value i) :=
  continuous_ordered_eigenvalue _ (fun X => (rightGram_posSemidef X).isHermitian)
    (continuous_rightGram d t) i

theorem continuous_singularValue (d t : ℕ) (i : Fin t) :
    Continuous (fun X : Matrix (Fin d) (Fin t) ℝ => singularValue X i) :=
  Real.continuous_sqrt.comp (continuous_gram_eigenvalue d t i)

theorem continuous_schattenPower (d t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    Continuous (schattenPower p : Matrix (Fin d) (Fin t) ℝ → ℝ) := by
  unfold schattenPower
  exact continuous_finset_sum _ (fun i _ =>
    (continuous_singularValue d t i).rpow_const (fun _ => Or.inr hp))

theorem continuous_schattenNorm (d t : ℕ) {p : ℝ} (hp : 0 < p) :
    Continuous (schattenNorm p : Matrix (Fin d) (Fin t) ℝ → ℝ) :=
  (continuous_schattenPower d t hp.le).rpow_const (fun _ => Or.inr (by positivity))

theorem continuous_optimalSchattenPower (d t k : ℕ) (hk : k ≤ t) {p : ℝ} (hp : 0 < p) :
    Continuous (fun H : Matrix (Fin d) (Fin t) ℝ => optimalSchattenPower p H k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have heq : (fun H : Matrix (Fin d) (Fin (k + m)) ℝ => optimalSchattenPower p H k) =
      fun H => ∑ i : Fin m,
        (orderedMatrixSpectrum (rightGram_posSemidef H).isHermitian).value
          (i.castLE (by omega)) ^ (p / 2) := by
    funext H
    exact optimalSchattenPower_eq_bottom hp H
  rw [heq]
  exact continuous_finset_sum _ (fun i _ =>
    (continuous_gram_eigenvalue d (k + m) (i.castLE (by omega))).rpow_const
      (fun _ => Or.inr (by positivity)))

theorem continuous_optimalSchattenNorm (d t k : ℕ) (hk : k ≤ t) {p : ℝ} (hp : 0 < p) :
    Continuous (fun H : Matrix (Fin d) (Fin t) ℝ => optimalSchattenNorm p H k) :=
  (continuous_optimalSchattenPower d t k hk hp).rpow_const (fun _ => Or.inr (by positivity))

end
end LowRank
