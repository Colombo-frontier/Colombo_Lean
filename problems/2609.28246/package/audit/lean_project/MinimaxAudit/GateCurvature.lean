import Mathlib

/-!
# Gate Hessian algebra and curvature under compression

The explicit two-dimensional symmetric matrix below is the Hessian formula in
manuscript lines 476--483. This file proves its eigenvector identities and
Euclidean contraction estimate for arbitrary coefficients in [0,1]. Identifying
this matrix with the Fréchet Hessian of the integral gate remains a separate
calculus obligation; that identity is not assumed to have been proved here.
-/

namespace MinimaxAudit

abbrev GatePlane := EuclideanSpace ℝ (Fin 2)

/-- Explicit matrix action H(x,y), with eigenvalues a and -b. -/
noncomputable def gateHessianAction (a b : ℝ) (v : GatePlane) : GatePlane :=
  WithLp.toLp 2 ![((a - b) * v 0 + (a + b) * v 1) / 2,
    ((a + b) * v 0 + (a - b) * v 1) / 2]

/-- The symmetric direction is an eigenvector with eigenvalue a. -/
theorem gateHessian_eigen_plus (a b : ℝ) :
    gateHessianAction a b (WithLp.toLp 2 ![1, 1]) =
      a • (WithLp.toLp 2 ![1, 1] : GatePlane) := by
  ext i
  fin_cases i <;> simp [gateHessianAction]

/-- The antisymmetric direction is an eigenvector with eigenvalue -b. -/
theorem gateHessian_eigen_minus (a b : ℝ) :
    gateHessianAction a b (WithLp.toLp 2 ![1, -1]) =
      (-b) • (WithLp.toLp 2 ![1, -1] : GatePlane) := by
  ext i
  fin_cases i <;> simp [gateHessianAction] <;> ring

/-- Spectral energy identity, with no range assumption on a or b. -/
theorem gateHessian_energy (a b : ℝ) (v : GatePlane) :
    ‖gateHessianAction a b v‖ ^ 2 =
      a ^ 2 * (v 0 + v 1) ^ 2 / 2 + b ^ 2 * (v 0 - v 1) ^ 2 / 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, gateHessianAction,
    Real.norm_eq_abs, sq_abs]
  ring

/-- Scalar identity for the Euclidean norm on the two-dimensional gate plane. -/
theorem gatePlane_norm_sq (v : GatePlane) :
    ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/-- The gate Hessian contracts every Euclidean vector when both cutoff values
lie in [0,1]. This is an all-vector estimate, not a sampled numerical check. -/
theorem gateHessian_norm_le {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (v : GatePlane) :
    ‖gateHessianAction a b v‖ ≤ ‖v‖ := by
  have ha2 : a ^ 2 ≤ 1 := by nlinarith
  have hb2 : b ^ 2 ≤ 1 := by nlinarith
  have hp := mul_le_mul_of_nonneg_right ha2 (sq_nonneg (v 0 + v 1))
  have hm := mul_le_mul_of_nonneg_right hb2 (sq_nonneg (v 0 - v 1))
  have he := gateHessian_energy a b v
  have hn := gatePlane_norm_sq v
  have hnonneg := norm_nonneg (gateHessianAction a b v)
  have hvnonneg := norm_nonneg v
  nlinarith

/-- The matrix action as a linear map. -/
noncomputable def gateHessianLinear (a b : ℝ) : GatePlane →ₗ[ℝ] GatePlane where
  toFun := gateHessianAction a b
  map_add' := by
    intro v w
    ext i
    fin_cases i <;> simp [gateHessianAction] <;> ring
  map_smul' := by
    intro c v
    ext i
    fin_cases i <;> simp [gateHessianAction] <;> ring

/-- Finite-dimensional continuity of the explicit Hessian action. -/
noncomputable def gateHessianCLM (a b : ℝ) : GatePlane →L[ℝ] GatePlane :=
  (gateHessianLinear a b).toContinuousLinearMap

/-- The manuscript gate Hessian's operator-norm bound, after the explicit
matrix has been identified by calculus. -/
theorem gateHessian_opNorm_le {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ‖gateHessianCLM a b‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa [gateHessianCLM, gateHessianLinear] using
    gateHessian_norm_le ha0 ha1 hb0 hb1 v

section BlockDiagonal

variable {J : Type*} [Fintype J]

/-- Extract one orthogonal two-dimensional block from a finite Euclidean sum. -/
noncomputable def gateBlockVector (v : EuclideanSpace ℝ (J × Fin 2)) (j : J) :
    GatePlane := WithLp.toLp 2 (fun i => v (j, i))

/-- The orthogonal direct sum of any finite number of gate Hessian blocks. -/
noncomputable def gateBlockAction (a b : J → ℝ)
    (v : EuclideanSpace ℝ (J × Fin 2)) : EuclideanSpace ℝ (J × Fin 2) :=
  WithLp.toLp 2 (fun ji =>
    gateHessianAction (a ji.1) (b ji.1) (gateBlockVector v ji.1) ji.2)

/-- Pythagoras for the arbitrary finite block decomposition. -/
theorem gateBlock_norm_sq (v : EuclideanSpace ℝ (J × Fin 2)) :
    ‖v‖ ^ 2 = ∑ j : J, ‖gateBlockVector v j‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, gateBlockVector, Fintype.sum_prod_type]

/-- Pythagoras applied after the block Hessian action. -/
theorem gateBlock_action_norm_sq (a b : J → ℝ)
    (v : EuclideanSpace ℝ (J × Fin 2)) :
    ‖gateBlockAction a b v‖ ^ 2 =
      ∑ j : J, ‖gateHessianAction (a j) (b j) (gateBlockVector v j)‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, gateBlockAction, Fintype.sum_prod_type]

/-- The direct-sum Hessian estimate is independent of the number of modules.
This closes the finite orthogonal-block norm algebra for every finite chain. -/
theorem gateBlock_norm_le (a b : J → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ 1) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1)
    (v : EuclideanSpace ℝ (J × Fin 2)) :
    ‖gateBlockAction a b v‖ ≤ ‖v‖ := by
  have hsquares :
      (∑ j : J, ‖gateHessianAction (a j) (b j) (gateBlockVector v j)‖ ^ 2) ≤
        ∑ j : J, ‖gateBlockVector v j‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    have h := gateHessian_norm_le (ha j).1 (ha j).2 (hb j).1 (hb j).2
      (gateBlockVector v j)
    have h1 := norm_nonneg (gateHessianAction (a j) (b j) (gateBlockVector v j))
    have h2 := norm_nonneg (gateBlockVector v j)
    nlinarith
  rw [← gateBlock_action_norm_sq, ← gateBlock_norm_sq] at hsquares
  have h1 := norm_nonneg (gateBlockAction a b v)
  have h2 := norm_nonneg v
  nlinarith

end BlockDiagonal

section Compression

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A norm-bounded Hessian compressed through a contraction has a quadratic
form bounded by q times the ambient squared norm. -/
theorem compressed_quadratic_le (H : F →L[ℝ] F) (B : E →L[ℝ] F)
    {q : ℝ} (hq : 0 ≤ q) (hH : ‖H‖ ≤ q) (hB : ‖B‖ ≤ 1) (v : E) :
    inner ℝ (H (B v)) (B v) ≤ q * ‖v‖ ^ 2 := by
  have hcs := real_inner_le_norm (H (B v)) (B v)
  have hHnorm := H.le_opNorm (B v)
  have hBnorm := B.le_opNorm v
  have hHnorm' : ‖H (B v)‖ ≤ q * ‖B v‖ := by
    exact hHnorm.trans (mul_le_mul_of_nonneg_right hH (norm_nonneg _))
  have hBnorm' : ‖B v‖ ≤ ‖v‖ := by
    have h := mul_le_mul_of_nonneg_right hB (norm_nonneg v)
    nlinarith
  have hfirst := mul_le_mul_of_nonneg_right hHnorm' (norm_nonneg (B v))
  have hsecond : ‖B v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    have h1 := norm_nonneg (B v)
    have h2 := norm_nonneg v
    nlinarith
  have hthird := mul_le_mul_of_nonneg_left hsecond hq
  nlinarith

/-- The lower curvature λ(1-q) survives compression by any contraction.
Applied to the x-block Hessian identity, this is the manuscript strong convexity
algebra; applied with the opposite sign it is strong concavity algebra. -/
theorem compressed_strong_curvature (H : F →L[ℝ] F) (B : E →L[ℝ] F)
    {q lam : ℝ} (hq : 0 ≤ q) (hlam : 0 ≤ lam)
    (hH : ‖H‖ ≤ q) (hB : ‖B‖ ≤ 1) (v : E) :
    lam * (1 - q) * ‖v‖ ^ 2 ≤
      lam * (‖v‖ ^ 2 - inner ℝ (H (B v)) (B v)) := by
  have h := compressed_quadratic_le H B hq hH hB v
  have hmul := mul_le_mul_of_nonneg_left h hlam
  nlinarith

end Compression

end MinimaxAudit
