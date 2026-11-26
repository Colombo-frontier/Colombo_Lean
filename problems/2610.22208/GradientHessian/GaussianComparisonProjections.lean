import GradientHessian.GaussianFrobeniusLaw

/-! Actual matrix, scalar and vector marginals of the Gaussian comparison
experiment, with exact bilinear identities and Gaussian distribution transport. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open Matrix MeasureTheory ProbabilityTheory GaussianHilbert
open scoped Matrix BigOperators InnerProductSpace

def coordinateProjection {I J : Type*} [Fintype I] [Fintype J] (f : J → I) :
    EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ J :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => (WithLp.equiv 2 _).symm (fun j => z (f j))
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

def comparisonMatrix (a b : ℕ) : MatrixComparisonSpace a b →L[ℝ] FrobeniusSpace a b :=
  coordinateProjection (fun p => Sum.inl (Sum.inl p))

def comparisonRow (a b : ℕ) : MatrixComparisonSpace a b →L[ℝ] EuclideanSpace ℝ (Fin a) :=
  coordinateProjection (fun i => Sum.inr (Sum.inl i))

def comparisonColumn (a b : ℕ) : MatrixComparisonSpace a b →L[ℝ] EuclideanSpace ℝ (Fin b) :=
  coordinateProjection (fun j => Sum.inr (Sum.inr j))

def comparisonScalar (a b : ℕ) : MatrixComparisonSpace a b →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => z (Sum.inl (Sum.inr ()))
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

def comparisonMatrixLift {a b : ℕ} (x : FrobeniusSpace a b) : MatrixComparisonSpace a b :=
  (WithLp.equiv 2 _).symm (Sum.elim (Sum.elim (fun p => x p) (fun _ => 0)) (fun _ => 0))

def comparisonRowLift {a b : ℕ} (x : EuclideanSpace ℝ (Fin a)) : MatrixComparisonSpace a b :=
  (WithLp.equiv 2 _).symm (Sum.elim (fun _ => 0) (Sum.elim (fun i => x i) (fun _ => 0)))

def comparisonColumnLift {a b : ℕ} (x : EuclideanSpace ℝ (Fin b)) : MatrixComparisonSpace a b :=
  (WithLp.equiv 2 _).symm (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun j => x j)))

theorem comparisonMatrix_dual (a b : ℕ) (z : MatrixComparisonSpace a b) (x : FrobeniusSpace a b) :
    ⟪comparisonMatrix a b z,x⟫_ℝ=⟪z,comparisonMatrixLift x⟫_ℝ := by
  simp [PiLp.inner_apply,comparisonMatrix,coordinateProjection,comparisonMatrixLift,Fintype.sum_sum_type]

theorem comparisonRow_dual (a b : ℕ) (z : MatrixComparisonSpace a b) (x : EuclideanSpace ℝ (Fin a)) :
    ⟪comparisonRow a b z,x⟫_ℝ=⟪z,comparisonRowLift x⟫_ℝ := by
  simp [PiLp.inner_apply,comparisonRow,coordinateProjection,comparisonRowLift,Fintype.sum_sum_type]

theorem comparisonColumn_dual (a b : ℕ) (z : MatrixComparisonSpace a b) (x : EuclideanSpace ℝ (Fin b)) :
    ⟪comparisonColumn a b z,x⟫_ℝ=⟪z,comparisonColumnLift x⟫_ℝ := by
  simp [PiLp.inner_apply,comparisonColumn,coordinateProjection,comparisonColumnLift,Fintype.sum_sum_type]

theorem comparisonMatrixLift_norm {a b : ℕ} (x : FrobeniusSpace a b) : ‖comparisonMatrixLift x‖=‖x‖ := by
  have h : ‖comparisonMatrixLift x‖^2=‖x‖^2 := by
    simp [← real_inner_self_eq_norm_sq,PiLp.inner_apply,comparisonMatrixLift,Fintype.sum_sum_type]
  nlinarith [norm_nonneg (comparisonMatrixLift x),norm_nonneg x]

theorem comparisonRowLift_norm {a b : ℕ} (x : EuclideanSpace ℝ (Fin a)) :
    ‖comparisonRowLift (b := b) x‖=‖x‖ := by
  have h : ‖comparisonRowLift (b := b) x‖^2=‖x‖^2 := by
    simp [← real_inner_self_eq_norm_sq,PiLp.inner_apply,comparisonRowLift,Fintype.sum_sum_type]
  nlinarith [norm_nonneg (comparisonRowLift (b := b) x),norm_nonneg x]

theorem comparisonColumnLift_norm {a b : ℕ} (x : EuclideanSpace ℝ (Fin b)) :
    ‖comparisonColumnLift (a := a) x‖=‖x‖ := by
  have h : ‖comparisonColumnLift (a := a) x‖^2=‖x‖^2 := by
    simp [← real_inner_self_eq_norm_sq,PiLp.inner_apply,comparisonColumnLift,Fintype.sum_sum_type]
  nlinarith [norm_nonneg (comparisonColumnLift (a := a) x),norm_nonneg x]

theorem comparisonMatrix_law (a b : ℕ) :
    (euclideanGaussianLaw (MatrixComparisonSpace a b)).map (comparisonMatrix a b)=
      euclideanGaussianLaw (FrobeniusSpace a b) :=
  gaussian_projection_law _ _ (comparisonMatrix_dual a b) comparisonMatrixLift_norm

theorem comparisonRow_law (a b : ℕ) :
    (euclideanGaussianLaw (MatrixComparisonSpace a b)).map (comparisonRow a b)=
      euclideanGaussianLaw (EuclideanSpace ℝ (Fin a)) :=
  gaussian_projection_law _ _ (comparisonRow_dual a b) comparisonRowLift_norm

theorem comparisonColumn_law (a b : ℕ) :
    (euclideanGaussianLaw (MatrixComparisonSpace a b)).map (comparisonColumn a b)=
      euclideanGaussianLaw (EuclideanSpace ℝ (Fin b)) :=
  gaussian_projection_law _ _ (comparisonColumn_dual a b) comparisonColumnLift_norm

theorem gaussian_linear_mean_zero {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (f : E →L[ℝ] ℝ) : (∫ z,f z ∂euclideanGaussianLaw E)=0 := by
  let U : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.neg ℝ
  have hp : MeasurePreserving U (euclideanGaussianLaw E) (euclideanGaussianLaw E) :=
    ⟨U.continuous.measurable,euclideanGaussian_isometry E U⟩
  have h := hp.integral_comp U.toHomeomorph.measurableEmbedding (fun z => f z)
  have he : (fun z => f (U z))=fun z => -f z := by funext z; exact map_neg f z
  rw [he,integral_neg] at h
  linarith

theorem comparisonScalar_mean (a b : ℕ) :
    (∫ z,comparisonScalar a b z ∂euclideanGaussianLaw (MatrixComparisonSpace a b))=0 :=
  gaussian_linear_mean_zero _

theorem matrixComparisonX_projection {a b : ℕ} (u : EuclideanSpace ℝ (Fin b))
    (v : EuclideanSpace ℝ (Fin a)) (z : MatrixComparisonSpace a b) :
    ⟪matrixComparisonX u v,z⟫_ℝ=
      ⟪v,LowRank.matrixEuclideanMap (matrixEntries a b (comparisonMatrix a b z)) u⟫_ℝ+
        comparisonScalar a b z := by
  simp only [LowRank.matrixEuclideanMap_inner]
  simp [PiLp.inner_apply,matrixComparisonX,Fintype.sum_sum_type,Fintype.sum_prod_type,
    RCLike.inner_apply,comparisonScalar,matrixEntries,comparisonMatrix,coordinateProjection,
    Matrix.mulVec,dotProduct,Finset.mul_sum]
  congr 1
  funext i
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem matrixComparisonY_projection {a b : ℕ} (u : EuclideanSpace ℝ (Fin b))
    (v : EuclideanSpace ℝ (Fin a)) (z : MatrixComparisonSpace a b) :
    ⟪matrixComparisonY u v,z⟫_ℝ=⟪v,comparisonRow a b z⟫_ℝ+⟪u,comparisonColumn a b z⟫_ℝ := by
  simp [PiLp.inner_apply,matrixComparisonY,Fintype.sum_sum_type,comparisonRow,comparisonColumn,
    coordinateProjection]

theorem projection_norm_le_one {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : E →L[ℝ] F) (lift : F → E) (hdual : ∀ x y,⟪f x,y⟫_ℝ=⟪x,lift y⟫_ℝ)
    (hnorm : ∀ y,‖lift y‖=‖y‖) : ‖f‖≤1 := by
  apply f.opNorm_le_bound (by norm_num)
  intro x
  have h := real_inner_le_norm x (lift (f x))
  rw [← hdual,real_inner_self_eq_norm_sq,hnorm] at h
  have hx := norm_nonneg x
  have hf := norm_nonneg (f x)
  nlinarith

theorem norm_comparisonMatrix_le_one (a b : ℕ) : ‖comparisonMatrix a b‖≤1 :=
  projection_norm_le_one _ _ (comparisonMatrix_dual a b) comparisonMatrixLift_norm

theorem norm_comparisonRow_le_one (a b : ℕ) : ‖comparisonRow a b‖≤1 :=
  projection_norm_le_one _ _ (comparisonRow_dual a b) comparisonRowLift_norm

theorem norm_comparisonColumn_le_one (a b : ℕ) : ‖comparisonColumn a b‖≤1 :=
  projection_norm_le_one _ _ (comparisonColumn_dual a b) comparisonColumnLift_norm

end GradientHessian.GaussianConcentration
