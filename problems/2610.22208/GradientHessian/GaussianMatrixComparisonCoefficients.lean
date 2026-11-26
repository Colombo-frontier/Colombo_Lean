import GradientHessian.GaussianHilbert

/-! The literal coefficient vectors for the matrix Gaussian comparison:
matrix bilinear form plus an independent scalar, versus two independent
Gaussian vector linear forms. All covariance identities are explicit. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open scoped BigOperators InnerProductSpace

abbrev MatrixComparisonIndex (a b : ℕ) := ((Fin a × Fin b) ⊕ Unit) ⊕ (Fin a ⊕ Fin b)
abbrev MatrixComparisonSpace (a b : ℕ) := EuclideanSpace ℝ (MatrixComparisonIndex a b)

def matrixComparisonX {a b : ℕ} (u : EuclideanSpace ℝ (Fin b)) (v : EuclideanSpace ℝ (Fin a)) :
    MatrixComparisonSpace a b :=
  (WithLp.equiv 2 _).symm (Sum.elim (Sum.elim (fun p : Fin a × Fin b => v p.1 * u p.2) (fun _ : Unit => 1))
    (fun _ : Fin a ⊕ Fin b => 0))

def matrixComparisonY {a b : ℕ} (u : EuclideanSpace ℝ (Fin b)) (v : EuclideanSpace ℝ (Fin a)) :
    MatrixComparisonSpace a b :=
  (WithLp.equiv 2 _).symm (Sum.elim (fun _ : (Fin a × Fin b) ⊕ Unit => 0) (Sum.elim (fun i => v i) (fun j => u j)))

theorem matrixComparison_cross {a b : ℕ} (u u' : EuclideanSpace ℝ (Fin b))
    (v v' : EuclideanSpace ℝ (Fin a)) : ⟪matrixComparisonX u v, matrixComparisonY u' v'⟫_ℝ = 0 := by
  simp [PiLp.inner_apply, matrixComparisonX, matrixComparisonY, Fintype.sum_sum_type]

theorem matrixComparisonY_inner {a b : ℕ} (u u' : EuclideanSpace ℝ (Fin b))
    (v v' : EuclideanSpace ℝ (Fin a)) :
    ⟪matrixComparisonY u v, matrixComparisonY u' v'⟫_ℝ = ⟪v,v'⟫_ℝ + ⟪u,u'⟫_ℝ := by
  simp [PiLp.inner_apply, matrixComparisonY, Fintype.sum_sum_type]

theorem matrixComparisonX_inner {a b : ℕ} (u u' : EuclideanSpace ℝ (Fin b))
    (v v' : EuclideanSpace ℝ (Fin a)) :
    ⟪matrixComparisonX u v, matrixComparisonX u' v'⟫_ℝ = ⟪v,v'⟫_ℝ * ⟪u,u'⟫_ℝ + 1 := by
  simp [PiLp.inner_apply, matrixComparisonX, Fintype.sum_sum_type, RCLike.inner_apply]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  congr 1
  funext i
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem matrixComparison_covariance_difference {a b : ℕ} (u u' : EuclideanSpace ℝ (Fin b))
    (v v' : EuclideanSpace ℝ (Fin a)) :
    ⟪matrixComparisonX u v, matrixComparisonX u' v'⟫_ℝ -
      ⟪matrixComparisonY u v, matrixComparisonY u' v'⟫_ℝ =
      (1 - ⟪u,u'⟫_ℝ) * (1 - ⟪v,v'⟫_ℝ) := by
  rw [matrixComparisonX_inner, matrixComparisonY_inner]
  ring

theorem matrixComparison_covariance_order {a b : ℕ} (u u' : EuclideanSpace ℝ (Fin b))
    (v v' : EuclideanSpace ℝ (Fin a)) (hu : ‖u‖=1) (hu' : ‖u'‖=1)
    (hv : ‖v‖=1) (hv' : ‖v'‖=1) :
    ⟪matrixComparisonY u v, matrixComparisonY u' v'⟫_ℝ ≤
      ⟪matrixComparisonX u v, matrixComparisonX u' v'⟫_ℝ := by
  apply sub_nonneg.mp
  rw [matrixComparison_covariance_difference]
  have h1 := real_inner_le_norm u u'
  have h2 := real_inner_le_norm v v'
  rw [hu, hu', one_mul] at h1
  rw [hv, hv', one_mul] at h2
  exact mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)

theorem matrixComparison_same_row {a b : ℕ} (u : EuclideanSpace ℝ (Fin b))
    (v v' : EuclideanSpace ℝ (Fin a)) (hu : ‖u‖=1) :
    ⟪matrixComparisonX u v, matrixComparisonX u v'⟫_ℝ =
      ⟪matrixComparisonY u v, matrixComparisonY u v'⟫_ℝ := by
  have h := matrixComparison_covariance_difference u u v v'
  rw [real_inner_self_eq_norm_sq, hu, one_pow, sub_self, zero_mul] at h
  exact sub_eq_zero.mp h

end GradientHessian.GaussianConcentration
