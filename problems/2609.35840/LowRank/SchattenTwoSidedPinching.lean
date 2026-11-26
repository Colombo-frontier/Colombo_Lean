import LowRank.HermitianDilation

/-! Two-sided Schatten pinching for all p at least one. A right subspace
containing the transpose image of a left subspace turns captured left power
into a bound on the actual right-projection residual. -/

namespace LowRank
open Matrix
open scoped Matrix
noncomputable section

theorem schattenPower_two_sided_pinching {a b : ℕ} {p : ℝ} (hp : 1 ≤ p)
    (A : Matrix (Fin a) (Fin b) ℝ)
    {P : Matrix (Fin a) (Fin a) ℝ} (hP : IsOrthogonalProjector P)
    {Q : Matrix (Fin b) (Fin b) ℝ} (hQ : IsOrthogonalProjector Q) :
    schattenPower p (P * A * Q) + schattenPower p ((1 - P) * A * (1 - Q)) ≤ schattenPower p A := by
  have hp0 : 0 < p := by linarith
  have h := symmetricAbsPowerTrace_projector_pinching (hermitianDilation_isHermitian A)
    (finBlocks_projector hP hQ) hp
  rw [symmetricAbsPowerTrace_congr _ (hermitianDilation_isHermitian (P * A * Q))
    (hermitianDilation_sandwich A hP hQ) p,
    symmetricAbsPowerTrace_congr _ (hermitianDilation_isHermitian ((1 - P) * A * (1 - Q)))
    (hermitianDilation_complement_sandwich A hP hQ) p] at h
  simp only [hermitianDilation_absPowerTrace _ hp0] at h
  linarith

theorem schattenPower_residual_le_sub_left_capture {a b : ℕ} {p : ℝ} (hp : 1 ≤ p)
    (A : Matrix (Fin a) (Fin b) ℝ)
    {P : Matrix (Fin a) (Fin a) ℝ} (hP : IsOrthogonalProjector P)
    {Q : Matrix (Fin b) (Fin b) ℝ} (hQ : IsOrthogonalProjector Q)
    (hsupport : Q * (Aᵀ * P) = Aᵀ * P) :
    schattenPower p (A * (1 - Q)) ≤ schattenPower p A - schattenPower p (P * A) := by
  have hPAQ : P * A * Q = P * A := by
    have h := congrArg Matrix.transpose hsupport
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hP.symmetric, hQ.symmetric] using h
  have hres : (1 - P) * A * (1 - Q) = A * (1 - Q) := by
    calc
      _ = A * (1 - Q) - (P * A - P * A * Q) := by
        simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]
        abel
      _ = _ := by rw [hPAQ, sub_self, sub_zero]
  have h := schattenPower_two_sided_pinching hp A hP hQ
  rw [hPAQ, hres] at h
  linarith

theorem schattenPower_left_column_projector {a b k : ℕ} {p : ℝ} (hp : 0 < p)
    (A : Matrix (Fin a) (Fin b) ℝ) (W : Matrix (Fin a) (Fin k) ℝ) (hW : Wᵀ * W = 1) :
    schattenPower p (W * Wᵀ * A) = schattenPower p (Aᵀ * W) := by
  calc
    _ = schattenPower p (W * Wᵀ * A)ᵀ := (schattenPower_transpose hp _).symm
    _ = schattenPower p ((Aᵀ * W) * Wᵀ) := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = _ := schattenPower_right_extension hp _ W hW

theorem schattenPower_right_refinement_residual {a b k : ℕ} {p : ℝ} (hp : 1 ≤ p)
    (A : Matrix (Fin a) (Fin b) ℝ) (W : Matrix (Fin a) (Fin k) ℝ) (hW : Wᵀ * W = 1)
    {Q : Matrix (Fin b) (Fin b) ℝ} (hQ : IsOrthogonalProjector Q)
    (hfix : Q * (Aᵀ * W) = Aᵀ * W) :
    schattenPower p (A * (1 - Q)) ≤ schattenPower p A - schattenPower p (Aᵀ * W) := by
  have hs : Q * (Aᵀ * (W * Wᵀ)) = Aᵀ * (W * Wᵀ) := by
    simpa only [Matrix.mul_assoc] using congrArg (fun B => B * Wᵀ) hfix
  have h := schattenPower_residual_le_sub_left_capture hp A (column_projector W hW) hQ hs
  rwa [schattenPower_left_column_projector (by linarith : 0 < p) A W hW] at h

end
end LowRank
