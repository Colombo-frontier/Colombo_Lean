import GradientHessian.GaussianConcentrationGenerator

/-! The full Gaussian Dirichlet identity for the actual generator and
Fréchet derivatives. Integrability assumptions state only growth conditions. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory ProbabilityTheory GaussianHilbert
open scoped InnerProductSpace BigOperators

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem covector_parseval (l : E →L[ℝ] ℝ) :
    (∑ i, (l (stdOrthonormalBasis ℝ E i)) ^ 2) = ‖l‖ ^ 2 := by
  have h := (stdOrthonormalBasis ℝ E).sum_sq_norm_inner ((InnerProductSpace.toDual ℝ E).symm l)
  have he (i) : ⟪stdOrthonormalBasis ℝ E i, (InnerProductSpace.toDual ℝ E).symm l⟫_ℝ =
      l (stdOrthonormalBasis ℝ E i) := by rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  simp_rw [he] at h
  simpa only [Real.norm_eq_abs,
    sq_abs, LinearIsometryEquiv.norm_map] using h

omit [MeasurableSpace E] [BorelSpace E] in
theorem weighted_generator_sum (u v : E → ℝ) (x : E) :
    u x * gaussianGenerator E v x =
      ∑ i, (u x * diagonalSecond E v i x -
        ⟪stdOrthonormalBasis ℝ E i, x⟫_ℝ * (u x * coordinateDerivative E v i x)) := by
  have hd : fderiv ℝ v x x =
      ∑ i, ⟪stdOrthonormalBasis ℝ E i, x⟫_ℝ * coordinateDerivative E v i x := by
    nth_rw 2 [← (stdOrthonormalBasis ℝ E).sum_repr' x]
    simp only [map_sum, map_smul, smul_eq_mul, coordinateDerivative]
  rw [gaussianGenerator, hd, mul_sub, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem gaussian_dirichlet {u v : E → ℝ} (hu : Differentiable ℝ u)
    (hv : ContDiff ℝ 2 v)
    (h0 : ∀ i, Integrable (fun x => u x * coordinateDerivative E v i x) (euclideanGaussianLaw E))
    (h1 : ∀ i, Integrable (fun x => coordinateDerivative E u i x * coordinateDerivative E v i x)
      (euclideanGaussianLaw E))
    (h2 : ∀ i, Integrable (fun x => u x * diagonalSecond E v i x) (euclideanGaussianLaw E))
    (hX : ∀ i, Integrable (fun x => ⟪stdOrthonormalBasis ℝ E i, x⟫_ℝ *
      (u x * coordinateDerivative E v i x)) (euclideanGaussianLaw E)) :
    (∫ x, u x * gaussianGenerator E v x ∂euclideanGaussianLaw E) =
      -(∫ x, ∑ i, coordinateDerivative E u i x * coordinateDerivative E v i x
        ∂euclideanGaussianLaw E) := by
  simp_rw [weighted_generator_sum]
  have hsub (i) : Integrable (fun x => u x * diagonalSecond E v i x -
      ⟪stdOrthonormalBasis ℝ E i, x⟫_ℝ * (u x * coordinateDerivative E v i x))
      (euclideanGaussianLaw E) := (h2 i).sub (hX i)
  rw [integral_finset_sum _ (fun i _ => hsub i),
    integral_finset_sum _ (fun i _ => h1 i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_sub (h2 i) (hX i)]
  exact gaussian_coordinate_green E hu hv i (h0 i) (h1 i) (h2 i) (hX i)

theorem gaussian_dirichlet_self {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (h0 : ∀ i, Integrable (fun x => f x * coordinateDerivative E f i x) (euclideanGaussianLaw E))
    (h1 : ∀ i, Integrable (fun x => (coordinateDerivative E f i x) ^ 2) (euclideanGaussianLaw E))
    (h2 : ∀ i, Integrable (fun x => f x * diagonalSecond E f i x) (euclideanGaussianLaw E))
    (hX : ∀ i, Integrable (fun x => ⟪stdOrthonormalBasis ℝ E i, x⟫_ℝ *
      (f x * coordinateDerivative E f i x)) (euclideanGaussianLaw E)) :
    (∫ x, f x * gaussianGenerator E f x ∂euclideanGaussianLaw E) =
      -(∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂euclideanGaussianLaw E) := by
  have hi := gaussian_dirichlet E (hf.differentiable (by norm_num)) hf h0
    (fun i => by simpa only [pow_two] using h1 i) h2 hX
  simpa only [← pow_two, coordinateDerivative, covector_parseval] using hi

end GradientHessian.GaussianConcentration
