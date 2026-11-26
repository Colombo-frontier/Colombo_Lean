import LowRank.FilteredGraphApproximation

/-! Weighted target blocks in filtered-range approximation. Diagonal target
weights commute with the normalizing filter. Singular-value weights can
therefore cancel the inverse scaling of a starting block's right inverse. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem frobeniusSq_mul_le {a b c : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (B : Matrix (Fin b) (Fin c) ℝ) :
    frobeniusSq (A * B) ≤ frobeniusSq A * frobeniusSq B := by
  simp only [frobeniusSq, Matrix.mul_apply]
  calc
    _ ≤ ∑ i, ∑ j, (∑ l, A i l ^ 2) * (∑ l, B l j ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => A i l) (fun l => B l j)
    _ = _ := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      congr 1
      exact Finset.sum_comm

theorem filteredTailBlock_mul_diagonal {m k s : ℕ} (w : Fin (m + k) → ℝ)
    (B : Matrix (Fin (m + k)) (Fin s) ℝ) (R : Matrix (Fin s) (Fin k) ℝ)
    (c : Fin k → ℝ) :
    filteredTailBlock w B R * diagonal c =
      diagonal (fun i => w (i.castAdd k)) *
        (B.submatrix (Fin.castAdd k) id * R * diagonal c) *
          diagonal (fun j => (w (j.natAdd m))⁻¹) := by
  ext i j
  simp only [filteredTailBlock, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

theorem filteredTailBlock_weighted_bound {m k s : ℕ} (w : Fin (m + k) → ℝ)
    (B : Matrix (Fin (m + k)) (Fin s) ℝ) (R : Matrix (Fin s) (Fin k) ℝ)
    (c : Fin k → ℝ) {η : ℝ} (hη : 0 ≤ η)
    (hl : ∀ i : Fin m, |w (i.castAdd k)| ≤ η) (hh : ∀ j : Fin k, 1 ≤ w (j.natAdd m)) :
    frobeniusSq (filteredTailBlock w B R * diagonal c) ≤
      η ^ 2 * frobeniusSq (B.submatrix (Fin.castAdd k) id * R * diagonal c) := by
  rw [filteredTailBlock_mul_diagonal]
  apply frobeniusSq_diagonal_sandwich_le _ _ _ hη hl
  intro j
  rw [abs_inv, abs_of_nonneg (by linarith [hh j] : 0 ≤ w (j.natAdd m))]
  exact inv_le_one_of_one_le₀ (hh j)

theorem filtered_weighted_residual_bound {d m k s : ℕ}
    (V : Matrix (Fin d) (Fin (m + k)) ℝ) (hV : Vᵀ * V = 1)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    (w : Fin (m + k) → ℝ) (B : Matrix (Fin (m + k)) (Fin s) ℝ)
    (R : Matrix (Fin s) (Fin k) ℝ) (hR : B.submatrix (Fin.natAdd m) id * R = 1)
    (hfix : P * (V * (diagonal w * B)) = V * (diagonal w * B))
    (c : Fin k → ℝ) {η : ℝ} (hη : 0 ≤ η)
    (hl : ∀ i : Fin m, |w (i.castAdd k)| ≤ η) (hh : ∀ j : Fin k, 1 ≤ w (j.natAdd m)) :
    frobeniusSq ((1 - P) * (V.submatrix id (Fin.natAdd m) * diagonal c)) ≤
      η ^ 2 * frobeniusSq (B.submatrix (Fin.castAdd k) id * R * diagonal c) := by
  have hw : ∀ j : Fin k, w (j.natAdd m) ≠ 0 := fun j => ne_of_gt (by linarith [hh j])
  have hnormalized : P * (V * normalizedFilteredBlock w B R) = V * normalizedFilteredBlock w B R := by
    have h := congrArg (fun M => M * R * diagonal (fun j => (w (j.natAdd m))⁻¹)) hfix
    simpa only [normalizedFilteredBlock, Matrix.mul_assoc] using h
  rw [normalizedFilteredBlock_graph V w B R hR hw] at hnormalized
  have hweighted := congrArg (fun M => M * diagonal c) hnormalized
  simp only [Matrix.add_mul, Matrix.mul_assoc] at hweighted
  have hlow : (V.submatrix id (Fin.castAdd k))ᵀ * V.submatrix id (Fin.castAdd k) = 1 :=
    orthogonal_subcolumns V hV _ (fun _ _ h => Fin.ext (congrArg (fun z : Fin (m + k) => z.val) h))
  calc
    _ ≤ frobeniusSq (V.submatrix id (Fin.castAdd k) * (filteredTailBlock w B R * diagonal c)) :=
      frobeniusSq_residual_le_of_fixed_perturbation hP _ _ hweighted
    _ = frobeniusSq (filteredTailBlock w B R * diagonal c) := frobeniusSq_orthogonal_left _ hlow _
    _ ≤ _ := filteredTailBlock_weighted_bound w B R c hη hl hh

theorem diagonal_mul_reciprocal {k : ℕ} (c : Fin k → ℝ) (hc : ∀ j, c j ≠ 0) :
    diagonal c * diagonal (fun j => (c j)⁻¹) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  simp only [mul_inv_cancel₀ (hc _), Matrix.diagonal_one]

theorem filtered_scaled_residual_bound {d m k s : ℕ}
    (V : Matrix (Fin d) (Fin (m + k)) ℝ) (hV : Vᵀ * V = 1)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    (w : Fin (m + k) → ℝ) (B : Matrix (Fin (m + k)) (Fin s) ℝ)
    (G : Matrix (Fin k) (Fin s) ℝ) (R : Matrix (Fin s) (Fin k) ℝ)
    (c : Fin k → ℝ) (hc : ∀ j, c j ≠ 0)
    (hB : B.submatrix (Fin.natAdd m) id = diagonal c * G) (hR : G * R = 1)
    (hfix : P * (V * (diagonal w * B)) = V * (diagonal w * B))
    {η : ℝ} (hη : 0 ≤ η) (hl : ∀ i : Fin m, |w (i.castAdd k)| ≤ η)
    (hh : ∀ j : Fin k, 1 ≤ w (j.natAdd m)) :
    frobeniusSq ((1 - P) * (V.submatrix id (Fin.natAdd m) * diagonal c)) ≤
      η ^ 2 * frobeniusSq (B.submatrix (Fin.castAdd k) id * R) := by
  have hinv := diagonal_mul_reciprocal c hc
  have hinv' : diagonal (fun j => (c j)⁻¹) * diagonal c = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [inv_mul_cancel₀ (hc _), Matrix.diagonal_one]
  have hnorm : B.submatrix (Fin.natAdd m) id * (R * diagonal (fun j => (c j)⁻¹)) = 1 := by
    rw [hB, Matrix.mul_assoc, ← Matrix.mul_assoc G, hR, Matrix.one_mul, hinv]
  have h := filtered_weighted_residual_bound V hV hP w B
    (R * diagonal (fun j => (c j)⁻¹)) hnorm hfix c hη hl hh
  simpa only [Matrix.mul_assoc, hinv', Matrix.mul_one] using h

end
end LowRank
