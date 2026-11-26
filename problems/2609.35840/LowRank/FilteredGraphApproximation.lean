import LowRank.ProjectionApproximation
import LowRank.OptimalSpectralColumns

/-! Deterministic filtered-range approximation. A right inverse of the
starting block on the target coordinates normalizes the retained rows to
identity. Tail suppression then bounds the distance to the target subspace. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem matrix_mul_split_rows {d m k t : ℕ} (V : Matrix (Fin d) (Fin (m + k)) ℝ)
    (Y : Matrix (Fin (m + k)) (Fin t) ℝ) :
    V * Y = V.submatrix id (Fin.castAdd k) * Y.submatrix (Fin.castAdd k) id +
      V.submatrix id (Fin.natAdd m) * Y.submatrix (Fin.natAdd m) id := by
  ext i j
  exact Fin.sum_univ_add (fun l => V i l * Y l j)

def normalizedFilteredBlock {m k s : ℕ} (w : Fin (m + k) → ℝ)
    (B : Matrix (Fin (m + k)) (Fin s) ℝ) (R : Matrix (Fin s) (Fin k) ℝ) :
    Matrix (Fin (m + k)) (Fin k) ℝ :=
  diagonal w * (B * R) * diagonal (fun j => (w (j.natAdd m))⁻¹)

def filteredTailBlock {m k s : ℕ} (w : Fin (m + k) → ℝ)
    (B : Matrix (Fin (m + k)) (Fin s) ℝ) (R : Matrix (Fin s) (Fin k) ℝ) :
    Matrix (Fin m) (Fin k) ℝ :=
  diagonal (fun i => w (i.castAdd k)) * (B.submatrix (Fin.castAdd k) id * R) *
    diagonal (fun j => (w (j.natAdd m))⁻¹)

theorem normalizedFilteredBlock_head {m k s : ℕ} (w : Fin (m + k) → ℝ)
    (B : Matrix (Fin (m + k)) (Fin s) ℝ) (R : Matrix (Fin s) (Fin k) ℝ)
    (hR : B.submatrix (Fin.natAdd m) id * R = 1) (hw : ∀ j : Fin k, w (j.natAdd m) ≠ 0) :
    (normalizedFilteredBlock w B R).submatrix (Fin.natAdd m) id = 1 := by
  ext i j
  have h := congrFun (congrFun hR i) j
  change (B * R) (i.natAdd m) j = (1 : Matrix (Fin k) (Fin k) ℝ) i j at h
  simp only [normalizedFilteredBlock, Matrix.submatrix_apply, id_eq,
    Matrix.mul_diagonal, Matrix.diagonal_mul, h]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.one_apply_eq, mul_one, mul_inv_cancel₀ (hw i)]
  · simp only [Matrix.one_apply_ne hij, mul_zero, zero_mul]

theorem normalizedFilteredBlock_tail {m k s : ℕ} (w : Fin (m + k) → ℝ)
    (B : Matrix (Fin (m + k)) (Fin s) ℝ) (R : Matrix (Fin s) (Fin k) ℝ) :
    (normalizedFilteredBlock w B R).submatrix (Fin.castAdd k) id = filteredTailBlock w B R := by
  ext i j
  simp only [normalizedFilteredBlock, filteredTailBlock, Matrix.submatrix_apply, id_eq,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

theorem normalizedFilteredBlock_graph {d m k s : ℕ} (V : Matrix (Fin d) (Fin (m + k)) ℝ)
    (w : Fin (m + k) → ℝ) (B : Matrix (Fin (m + k)) (Fin s) ℝ)
    (R : Matrix (Fin s) (Fin k) ℝ) (hR : B.submatrix (Fin.natAdd m) id * R = 1)
    (hw : ∀ j : Fin k, w (j.natAdd m) ≠ 0) :
    V * normalizedFilteredBlock w B R = V.submatrix id (Fin.natAdd m) +
      V.submatrix id (Fin.castAdd k) * filteredTailBlock w B R := by
  rw [matrix_mul_split_rows, normalizedFilteredBlock_head w B R hR hw,
    normalizedFilteredBlock_tail, Matrix.mul_one, add_comm]

theorem filteredTailBlock_bound {m k s : ℕ} (w : Fin (m + k) → ℝ)
    (B : Matrix (Fin (m + k)) (Fin s) ℝ) (R : Matrix (Fin s) (Fin k) ℝ)
    {η : ℝ} (hη : 0 ≤ η) (hl : ∀ i : Fin m, |w (i.castAdd k)| ≤ η)
    (hh : ∀ j : Fin k, 1 ≤ w (j.natAdd m)) :
    frobeniusSq (filteredTailBlock w B R) ≤ η ^ 2 * frobeniusSq (B.submatrix (Fin.castAdd k) id * R) := by
  apply frobeniusSq_diagonal_sandwich_le _ _ _ hη hl
  intro j
  rw [abs_inv, abs_of_nonneg (by linarith [hh j] : 0 ≤ w (j.natAdd m))]
  exact inv_le_one_of_one_le₀ (hh j)

theorem filtered_subspace_residual_bound {d m k s : ℕ}
    (V : Matrix (Fin d) (Fin (m + k)) ℝ) (hV : Vᵀ * V = 1)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    (w : Fin (m + k) → ℝ) (B : Matrix (Fin (m + k)) (Fin s) ℝ)
    (R : Matrix (Fin s) (Fin k) ℝ) (hR : B.submatrix (Fin.natAdd m) id * R = 1)
    (hfix : P * (V * (diagonal w * B)) = V * (diagonal w * B))
    {η : ℝ} (hη : 0 ≤ η) (hl : ∀ i : Fin m, |w (i.castAdd k)| ≤ η)
    (hh : ∀ j : Fin k, 1 ≤ w (j.natAdd m)) :
    frobeniusSq ((1 - P) * V.submatrix id (Fin.natAdd m)) ≤
      η ^ 2 * frobeniusSq (B.submatrix (Fin.castAdd k) id * R) := by
  have hw : ∀ j : Fin k, w (j.natAdd m) ≠ 0 := fun j => ne_of_gt (by linarith [hh j])
  have hnormalized : P * (V * normalizedFilteredBlock w B R) = V * normalizedFilteredBlock w B R := by
    have h := congrArg (fun M => M * R * diagonal (fun j => (w (j.natAdd m))⁻¹)) hfix
    simpa only [normalizedFilteredBlock, Matrix.mul_assoc] using h
  rw [normalizedFilteredBlock_graph V w B R hR hw] at hnormalized
  have hlow : (V.submatrix id (Fin.castAdd k))ᵀ * V.submatrix id (Fin.castAdd k) = 1 :=
    orthogonal_subcolumns V hV _ (fun _ _ h => Fin.ext (congrArg (fun z : Fin (m + k) => z.val) h))
  calc
    _ ≤ frobeniusSq (V.submatrix id (Fin.castAdd k) * filteredTailBlock w B R) :=
      frobeniusSq_residual_le_of_fixed_perturbation hP _ _ hnormalized
    _ = frobeniusSq (filteredTailBlock w B R) := frobeniusSq_orthogonal_left _ hlow _
    _ ≤ _ := filteredTailBlock_bound w B R hη hl hh

end
end LowRank
