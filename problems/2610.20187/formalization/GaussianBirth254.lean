import GaussianHistory254

noncomputable section
open scoped Matrix BigOperators
open Matrix
namespace Paper254

def isotropicGaussian {d : ℕ} (m : Coordinates d) (D : ℝ) (hD : 0 < D) : PrecisionGaussian d :=
  ⟨m, Matrix.diagonal (fun _ => 1/D^2), Matrix.posDef_diagonal_iff.mpr (fun _ => by positivity)⟩

def birthBudget (d : ℕ) (D q : ℝ) : ℝ := (1+d*(q/D^2-1-Real.log (q/D^2)))/2

theorem diagonal_const_quadratic {d : ℕ} (c : ℝ) (x : Space d) :
    matrixQuadratic (Matrix.diagonal (fun _ => c)) x = c*‖x‖^2 := by
  simp only [matrixQuadratic, dotProduct, Matrix.mulVec_diagonal, EuclideanSpace.norm_sq_eq,
    Real.norm_eq_abs, sq_abs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem isotropicGaussian_covariance {d : ℕ} (m : Coordinates d) (D q : ℝ)
    (hD : 0 < D) (hq : 0 < q) :
    precisionCovariancePart q (isotropicGaussian m D hD).precision =
      d*(q/D^2-1-Real.log (q/D^2)) := by
  change q*(Matrix.diagonal (fun _ : Fin d => 1/D^2)).trace-d-
    Real.log (q^d*(Matrix.diagonal (fun _ : Fin d => 1/D^2)).det) = _
  simp only [Matrix.trace_diagonal, Matrix.det_diagonal, Finset.sum_const,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_pow, Real.log_pow]
  ring_nf

theorem isotropicGaussian_potential {d : ℕ} (m u : Space d) (D q : ℝ)
    (hD : 0 < D) (hq : 0 < q) :
    (isotropicGaussian m D hD).potential q u =
      (d*(q/D^2-1-Real.log (q/D^2))+‖u-m‖^2/D^2)/2 := by
  unfold PrecisionGaussian.potential
  rw [isotropicGaussian_covariance _ _ _ hD hq]
  have hsub : ((u-m : Space d) : Coordinates d) = (u : Coordinates d)-(m : Coordinates d) := by
    ext j
    rfl
  change (_+matrixQuadratic (Matrix.diagonal (fun _ => 1/D^2))
    ((u : Coordinates d)-(m : Coordinates d)))/2 = _
  rw [← hsub, diagonal_const_quadratic]
  ring

theorem isotropicGaussian_birth_bound {d : ℕ} {D : ℝ} (W : Domain d D)
    (hD : 0 < D) (m u : W.carrier) (q : ℝ) (hq : 0 < q) :
    (isotropicGaussian m.val D hD).potential q u.val ≤ birthBudget d D q := by
  rw [isotropicGaussian_potential _ _ _ _ hD hq]
  have hn := W.diameter u.val u.property m.val m.property
  have hs : ‖u.val-m.val‖^2 ≤ D^2 := by nlinarith [norm_nonneg (u.val-m.val)]
  have hr : ‖u.val-m.val‖^2/D^2 ≤ 1 := (div_le_one (sq_pos_of_pos hD)).mpr hs
  unfold birthBudget
  linarith

end Paper254
#print axioms Paper254.isotropicGaussian_birth_bound
