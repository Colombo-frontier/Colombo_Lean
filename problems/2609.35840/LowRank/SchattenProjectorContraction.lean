import LowRank.SchattenIsometry
import LowRank.ProjectorBasis

/-! Orthogonal projection on either side contracts positive Schatten powers.
The right-side argument factors a projector through an orthonormal basis,
so it also covers singular projectors and zero-dimensional ranges. -/

namespace LowRank
open Matrix
open scoped Matrix
noncomputable section

theorem schattenPower_right_projector_le {a b : ℕ} {p : ℝ} (hp : 0 < p)
    (A : Matrix (Fin a) (Fin b) ℝ) {P : Matrix (Fin b) (Fin b) ℝ}
    (hP : IsOrthogonalProjector P) : schattenPower p (A * P) ≤ schattenPower p A := by
  obtain ⟨B, hB, hBB⟩ := projector_basis_factorization hP rfl
  rw [← hBB, ← Matrix.mul_assoc, schattenPower_right_extension hp _ B hB]
  exact schattenPower_right_isometry_le hp.le A B hB

theorem schattenPower_left_projector_le {a b : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (A : Matrix (Fin a) (Fin b) ℝ) {P : Matrix (Fin a) (Fin a) ℝ}
    (hP : IsOrthogonalProjector P) : schattenPower p (P * A) ≤ schattenPower p A := by
  have hgram : (P * A)ᵀ * (P * A) = Aᵀ * P * A := by
    simp only [Matrix.transpose_mul, hP.symmetric, Matrix.mul_assoc,
      ← Matrix.mul_assoc P P, hP.idempotent]
  have horder : LoewnerLE ((P * A)ᵀ * (P * A)) (Aᵀ * A) := by
    rw [hgram]
    simpa only [Matrix.mul_one] using loewner_congruence hP.le_one A
  rw [schattenPower_eq_symmetricPowerTrace, schattenPower_eq_symmetricPowerTrace]
  exact symmetricPowerTrace_mono (rightGram_posSemidef _) (rightGram_posSemidef _) horder
    (by positivity)

theorem schattenPower_two_sided_projector_le {a b : ℕ} {p : ℝ} (hp : 0 < p)
    (A : Matrix (Fin a) (Fin b) ℝ)
    {P : Matrix (Fin a) (Fin a) ℝ} (hP : IsOrthogonalProjector P)
    {Q : Matrix (Fin b) (Fin b) ℝ} (hQ : IsOrthogonalProjector Q) :
    schattenPower p (P * A * Q) ≤ schattenPower p A :=
  (schattenPower_right_projector_le hp _ hQ).trans (schattenPower_left_projector_le hp.le A hP)

theorem schattenNorm_two_sided_projector_le {a b : ℕ} {p : ℝ} (hp : 0 < p)
    (A : Matrix (Fin a) (Fin b) ℝ)
    {P : Matrix (Fin a) (Fin a) ℝ} (hP : IsOrthogonalProjector P)
    {Q : Matrix (Fin b) (Fin b) ℝ} (hQ : IsOrthogonalProjector Q) :
    schattenNorm p (P * A * Q) ≤ schattenNorm p A :=
  Real.rpow_le_rpow (schattenPower_nonneg _ _)
    (schattenPower_two_sided_projector_le hp A hP hQ) (by positivity)

end
end LowRank
