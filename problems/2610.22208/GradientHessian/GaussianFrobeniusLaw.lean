import GradientHessian.GaussianMatrixComparisonCoefficients
import LowRank.GaussianOrthogonalCompression
import LowRank.MatrixNetBound

/-! The standard Gaussian law on Frobenius matrix coordinates is exactly
the original independent-entry matrix law, with continuous linear maps
in both directions. Gaussian marginal transport is proved by characteristic functions. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open Matrix MeasureTheory ProbabilityTheory GaussianHilbert
open scoped Matrix BigOperators InnerProductSpace

abbrev FrobeniusSpace (a b : ℕ) := EuclideanSpace ℝ (Fin a × Fin b)

def matrixVector (a b : ℕ) : Matrix (Fin a) (Fin b) ℝ →L[ℝ] FrobeniusSpace a b :=
  LinearMap.toContinuousLinearMap {
    toFun := fun X => (WithLp.equiv 2 _).symm (fun p => X p.1 p.2)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

def matrixEntries (a b : ℕ) : FrobeniusSpace a b →L[ℝ] Matrix (Fin a) (Fin b) ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z i j => z (i,j)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

@[simp] theorem matrixEntries_vector (a b : ℕ) (X : Matrix (Fin a) (Fin b) ℝ) :
    matrixEntries a b (matrixVector a b X)=X := rfl

@[simp] theorem matrixVector_entries (a b : ℕ) (z : FrobeniusSpace a b) :
    matrixVector a b (matrixEntries a b z)=z := rfl

theorem iidMatrix_standard_characteristic (a b : ℕ) (c : Matrix (Fin a) (Fin b) ℝ) :
    (∫ X,Complex.exp (((∑ i,c i ⬝ᵥ X i : ℝ) : ℂ)*Complex.I) ∂LowRank.iidMatrixLaw a b 1)=
      Complex.exp (-((∑ i,c i ⬝ᵥ c i : ℝ) : ℂ)/2) := by
  have he (X : Matrix (Fin a) (Fin b) ℝ) :
      Complex.exp (((∑ i,c i ⬝ᵥ X i : ℝ) : ℂ)*Complex.I)=
        ∏ i,Complex.exp (((c i ⬝ᵥ X i : ℝ) : ℂ)*Complex.I) := by
    rw [Complex.ofReal_sum,Finset.sum_mul,Complex.exp_sum]
  simp_rw [he]
  have hp : (∫ X,∏ i,Complex.exp (((c i ⬝ᵥ X i : ℝ) : ℂ)*Complex.I)
      ∂LowRank.iidMatrixLaw a b 1)=
      ∏ i,∫ x,Complex.exp (((c i ⬝ᵥ x : ℝ) : ℂ)*Complex.I) ∂LowRank.iidVectorLaw b 1 := by
    letI : MeasureSpace (Fin b → ℝ) := ⟨LowRank.iidVectorLaw b 1⟩
    letI : SigmaFinite (volume : Measure (Fin b → ℝ)) := by
      change SigmaFinite (LowRank.iidVectorLaw b 1)
      infer_instance
    exact integral_fintype_prod_eq_prod (Fin a) (fun i x => Complex.exp (((c i ⬝ᵥ x : ℝ) : ℂ)*Complex.I))
  rw [hp]
  simp_rw [LowRank.iidVectorLaw_characteristic,NNReal.coe_one,Complex.ofReal_one,neg_one_mul]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_sum,← Finset.sum_neg_distrib,← Finset.sum_div]

theorem matrixVector_gaussian_law (a b : ℕ) :
    (LowRank.iidMatrixLaw a b 1).map (matrixVector a b)=euclideanGaussianLaw (FrobeniusSpace a b) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply]
  have hf : StronglyMeasurable (fun z : FrobeniusSpace a b => Complex.exp ((⟪z,t⟫_ℝ : ℂ)*Complex.I)) :=
    (by fun_prop : Continuous _).stronglyMeasurable
  rw [integral_map_of_stronglyMeasurable (φ := fun X => matrixVector a b X)
    (matrixVector a b).continuous.measurable hf]
  have hi (X : Matrix (Fin a) (Fin b) ℝ) :
      ⟪matrixVector a b X,t⟫_ℝ=∑ i,(matrixEntries a b t i) ⬝ᵥ X i := by
    simp [PiLp.inner_apply,Fintype.sum_prod_type,RCLike.inner_apply,matrixVector,matrixEntries,dotProduct]
  simp_rw [hi]
  rw [iidMatrix_standard_characteristic,euclideanGaussian_characteristic]
  have hn : (∑ i,(matrixEntries a b t i) ⬝ᵥ (matrixEntries a b t i))=‖t‖^2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp [PiLp.inner_apply,Fintype.sum_prod_type,RCLike.inner_apply,matrixEntries,dotProduct]
  rw [hn,Complex.ofReal_pow]

theorem matrixEntries_gaussian_law (a b : ℕ) :
    (euclideanGaussianLaw (FrobeniusSpace a b)).map (matrixEntries a b)=LowRank.iidMatrixLaw a b 1 := by
  rw [← matrixVector_gaussian_law a b,Measure.map_map
    (g := fun z => matrixEntries a b z) (f := fun X => matrixVector a b X)
    (matrixEntries a b).continuous.measurable (matrixVector a b).continuous.measurable]
  simp only [Function.comp_def,matrixEntries_vector,Measure.map_id']

theorem gaussian_projection_law {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (f : E →L[ℝ] F) (lift : F → E) (hdual : ∀ x y,⟪f x,y⟫_ℝ=⟪x,lift y⟫_ℝ)
    (hnorm : ∀ y,‖lift y‖=‖y‖) :
    (euclideanGaussianLaw E).map f=euclideanGaussianLaw F := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply]
  have hf : StronglyMeasurable (fun z : F => Complex.exp ((⟪z,t⟫_ℝ : ℂ)*Complex.I)) :=
    (by fun_prop : Continuous _).stronglyMeasurable
  rw [integral_map_of_stronglyMeasurable f.measurable hf]
  simp_rw [hdual]
  change charFun (euclideanGaussianLaw E) (lift t)=_
  rw [euclideanGaussian_characteristic,euclideanGaussian_characteristic,hnorm]

end GradientHessian.GaussianConcentration
