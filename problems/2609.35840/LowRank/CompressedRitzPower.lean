import LowRank.RitzPowerDeficit
import LowRank.SchattenProjectorContraction

/-! Captured Schatten power of the actual compressed Ritz output, including
zero eigenvalues. Removing its zero compressed columns is a right orthogonal
projection of the original output matrix, which gives an inequality without
requiring every selected column to belong to the query space. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem optimalColumnSelector_zero_column {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (j : Fin k)
    (hj : (canonicalOrderedSpectrum b (symmetricRightGram A)).value
      (lastColumnIndex b k hk j) = 0) (i : Fin a) :
    (A * optimalColumnSelector a b k hk A) i j = 0 := by
  have he := (optimalColumnSelector_column_energy hk A j).trans hj
  have hi := Finset.single_le_sum (f := fun l => (A * optimalColumnSelector a b k hk A) l j ^ 2)
    (fun l _ => sq_nonneg _) (Finset.mem_univ i)
  rw [he] at hi
  exact sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg _))

theorem compressedRitz_mask_factorization {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {P : Matrix (Fin b) (Fin b) ℝ}
    (hP : IsOrthogonalProjector P) :
    let Z := optimalColumnSelector a b k hk (A * P)
    ∃ D : Matrix (Fin k) (Fin k) ℝ, IsOrthogonalProjector D ∧ (A * P) * Z = (A * Z) * D := by
  classical
  dsimp only
  let Z := optimalColumnSelector a b k hk (A * P)
  let e := fun j => (canonicalOrderedSpectrum b (symmetricRightGram (A * P))).value
    (lastColumnIndex b k hk j)
  let D : Matrix (Fin k) (Fin k) ℝ := diagonal (fun j => if e j = 0 then 0 else 1)
  refine ⟨D, ⟨Matrix.diagonal_transpose _, ?_⟩, ?_⟩
  · dsimp only [D]
    rw [Matrix.diagonal_mul_diagonal]
    apply congrArg diagonal
    funext j
    split_ifs <;> norm_num
  · change (A * P) * Z = (A * Z) * D
    ext i j
    rw [Matrix.mul_diagonal]
    by_cases hj : e j = 0
    · simp only [hj, ite_true, mul_zero]
      exact optimalColumnSelector_zero_column hk (A * P) j hj i
    · simp only [hj, ite_false, mul_one]
      have h := congrFun (congrArg (fun x => A *ᵥ x)
        (optimalColumnSelector_compressed_column_fixed hk A hP j hj)) i
      dsimp only at h
      rw [Matrix.mulVec_mulVec] at h
      exact h

theorem optimalColumnSelector_compressed_power_le {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {P : Matrix (Fin b) (Fin b) ℝ}
    (hP : IsOrthogonalProjector P) {p : ℝ} (hp : 0 < p) :
    schattenPower p ((A * P) * optimalColumnSelector a b k hk (A * P)) ≤
      schattenPower p (A * optimalColumnSelector a b k hk (A * P)) := by
  obtain ⟨D, hD, he⟩ := compressedRitz_mask_factorization hk A hP
  rw [he]
  exact schattenPower_right_projector_le hp _ hD

theorem compressedRitz_spectral_power_le {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {P : Matrix (Fin b) (Fin b) ℝ}
    (hP : IsOrthogonalProjector P) {p : ℝ} (hp : 0 < p) :
    (∑ j, ((canonicalOrderedSpectrum b (symmetricRightGram (A * P))).value
      (lastColumnIndex b k hk j)) ^ (p / 2)) ≤
      schattenPower p (A * optimalColumnSelector a b k hk (A * P)) := by
  rw [← optimalColumnSelector_schattenPower hk (A * P) p]
  exact optimalColumnSelector_compressed_power_le hk A hP hp

theorem compressedRitz_power_deficit_of_projector {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {P : Matrix (Fin b) (Fin b) ℝ}
    (hP : IsOrthogonalProjector P) {p : ℝ} (hp : 0 < p)
    (x e : Fin k → ℝ) (hx : ∀ j, 0 ≤ x j) (he : ∀ j, 0 ≤ e j)
    (happrox : ∀ j, x j - e j ≤ (canonicalOrderedSpectrum b (symmetricRightGram (A * P))).value
      (lastColumnIndex b k hk j)) :
    (∑ j, x j ^ (p / 2)) - (∑ j, max 1 (p / 2) * e j * x j ^ (p / 2 - 1)) ≤
      schattenPower p (A * optimalColumnSelector a b k hk (A * P)) :=
  (optimalColumnSelector_power_deficit hk (A * P) hp x e hx he happrox).trans
    (optimalColumnSelector_compressed_power_le hk A hP hp)

end
end LowRank
