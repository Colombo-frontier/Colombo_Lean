import Bilevel.OrthogonalHaar
import Bilevel.SphereLaw

/-! The matrix Haar group acts by genuine Euclidean linear isometries. -/
noncomputable section
open Matrix MeasureTheory
open scoped RealInnerProductSpace
namespace Bilevel.OrthogonalAction
open EuclideanGaussian

def linearEquiv (d : ℕ) (A : OrthogonalHaar.Group d) : Space d ≃ₗ[ℝ] Space d :=
  (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).trans
    ((Matrix.UnitaryGroup.toLinearEquiv A).trans (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm)

theorem equiv_apply (d : ℕ) (A : OrthogonalHaar.Group d) (x : Space d) :
    linearEquiv d A x = Matrix.toEuclideanLin A.val x := rfl

theorem inner_preserving (d : ℕ) (A : OrthogonalHaar.Group d) (x y : Space d) :
    ⟪linearEquiv d A x, linearEquiv d A y⟫ = ⟪x, y⟫ := by
  simp only [equiv_apply, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.piLp_equiv_toEuclideanLin_apply, star_trivial]
  have hA : A.valᵀ * A.val = 1 := A.property.1
  rw [dotProduct_mulVec, vecMul_mulVec, hA, vecMul_one]

def isometry (d : ℕ) (A : OrthogonalHaar.Group d) : Space d ≃ₗᵢ[ℝ] Space d :=
  (linearEquiv d A).isometryOfInner (inner_preserving d A)

@[simp] theorem isometry_apply (d : ℕ) (A : OrthogonalHaar.Group d) (x : Space d) :
    isometry d A x = Matrix.toEuclideanLin A.val x := rfl

theorem gaussian_preserving (d : ℕ) (A : OrthogonalHaar.Group d) :
    MeasurePreserving (isometry d A) (law d) (law d) :=
  EuclideanGaussian.orthogonal_invariance d (isometry d A)

theorem sphere_preserving (d : ℕ) (A : OrthogonalHaar.Group d) :
    MeasurePreserving (isometry d A) (SphereLaw.sphereLaw d) (SphereLaw.sphereLaw d) :=
  SphereLaw.orthogonal_invariance d (isometry d A)

theorem isometry_mul (d : ℕ) (A B : OrthogonalHaar.Group d) (x : Space d) :
    isometry d (A * B) x = isometry d A (isometry d B x) := by
  apply (WithLp.equiv 2 (Fin d → ℝ)).injective
  simp only [isometry_apply, Matrix.piLp_equiv_toEuclideanLin_apply,
    Matrix.UnitaryGroup.mul_val, Matrix.mulVec_mulVec]

theorem isometry_one (d : ℕ) (x : Space d) :
    isometry d 1 x = x := by
  apply (WithLp.equiv 2 (Fin d → ℝ)).injective
  simp only [isometry_apply, Matrix.piLp_equiv_toEuclideanLin_apply,
    Matrix.UnitaryGroup.one_val, Matrix.one_mulVec]

instance action (d : ℕ) : MulAction (OrthogonalHaar.Group d) (Space d) where
  smul A x := isometry d A x
  one_smul := isometry_one d
  mul_smul := isometry_mul d

@[simp] theorem action_apply (d : ℕ) (A : OrthogonalHaar.Group d) (x : Space d) :
    A • x = isometry d A x := rfl

theorem action_continuous (d : ℕ) :
    Continuous (fun p : OrthogonalHaar.Group d × Space d => p.1 • p.2) := by
  change Continuous (fun p : OrthogonalHaar.Group d × Space d =>
    (WithLp.equiv 2 (Fin d → ℝ)).symm (p.1.val *ᵥ (WithLp.equiv 2 (Fin d → ℝ)) p.2))
  have h₁ : Continuous (WithLp.equiv 2 (Fin d → ℝ)) := PiLp.continuous_equiv _ _
  have h₂ : Continuous (WithLp.equiv 2 (Fin d → ℝ)).symm := PiLp.continuous_equiv_symm _ _
  exact h₂.comp ((continuous_subtype_val.comp continuous_fst).matrix_mulVec (h₁.comp continuous_snd))

instance measurableAction (d : ℕ) : MeasurableSMul₂ (OrthogonalHaar.Group d) (Space d) :=
  ⟨(action_continuous d).measurable⟩

def matrixOfIsometry (d : ℕ) (U : Space d ≃ₗᵢ[ℝ] Space d) : OrthogonalHaar.Group d :=
  ⟨(EuclideanSpace.basisFun (Fin d) ℝ).toBasis.toMatrix ((EuclideanSpace.basisFun (Fin d) ℝ).map U),
    (EuclideanSpace.basisFun (Fin d) ℝ).toMatrix_orthonormalBasis_mem_orthogonal
      ((EuclideanSpace.basisFun (Fin d) ℝ).map U)⟩

theorem isometry_matrixOfIsometry (d : ℕ) (U : Space d ≃ₗᵢ[ℝ] Space d) (x : Space d) :
    isometry d (matrixOfIsometry d U) x = U x := by
  have hm : (matrixOfIsometry d U).val =
      LinearMap.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin d) ℝ).toBasis U.toLinearEquiv.toLinearMap := by
    ext i j
    simp [matrixOfIsometry, LinearMap.toMatrix_apply, Basis.toMatrix_apply,
      OrthonormalBasis.map_apply]
  rw [isometry_apply, hm, Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.toLin_toMatrix]
  rfl

theorem transitive_on_sphere (d : ℕ) (x y : Space d) (hxy : ‖x‖ = ‖y‖) :
    ∃ A : OrthogonalHaar.Group d, A • x = y := by
  let U : Space d ≃ₗᵢ[ℝ] Space d := (Submodule.span ℝ {x - y})ᗮ.reflection
  refine ⟨matrixOfIsometry d U, ?_⟩
  rw [action_apply, isometry_matrixOfIsometry]
  exact Submodule.reflection_sub hxy

end Bilevel.OrthogonalAction
