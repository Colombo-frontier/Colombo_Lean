import GradientHessian.GaussianComparison
import Mathlib.Algebra.BigOperators.Pi

/-! Contraction of the actual Hessian with the coordinate covariance
matrix, and an entrywise Gaussian comparison criterion. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert
open scoped InnerProductSpace BigOperators NNReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable {I : Type*} [Fintype I] [DecidableEq I]

def coordinateCovariance (A B : E →L[ℝ] (I → ℝ)) (i j : I) : ℝ :=
  ∑ k, A (stdOrthonormalBasis ℝ E k) i * B (stdOrthonormalBasis ℝ E k) j

omit [MeasurableSpace E] [BorelSpace E] [Fintype I] [DecidableEq I] in
theorem coordinateCovariance_swap (A B : E →L[ℝ] (I → ℝ)) (i j : I) :
    coordinateCovariance E A B i j = coordinateCovariance E B A j i := by
  unfold coordinateCovariance
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem bilinear_coordinate_expansion (H : (I → ℝ) →L[ℝ] (I → ℝ) →L[ℝ] ℝ)
    (u v : I → ℝ) :
    H u v = ∑ i, ∑ j, (u i * v j) * H (Pi.single i 1) (Pi.single j 1) := by
  have hu : u = ∑ i, u i • (Pi.single i (1 : ℝ) : I → ℝ) := by ext i; simp [Pi.single_apply]
  have hv : v = ∑ j, v j • (Pi.single j (1 : ℝ) : I → ℝ) := by ext j; simp [Pi.single_apply]
  conv_lhs => rw [hu, hv]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [MeasurableSpace E] [BorelSpace E] in
theorem bilinear_covariance_trace (A B : E →L[ℝ] (I → ℝ))
    (H : (I → ℝ) →L[ℝ] (I → ℝ) →L[ℝ] ℝ) :
    (∑ k, H (A (stdOrthonormalBasis ℝ E k)) (B (stdOrthonormalBasis ℝ E k))) =
      ∑ i, ∑ j, coordinateCovariance E A B i j * H (Pi.single i 1) (Pi.single j 1) := by
  calc
    _ = ∑ k, ∑ i, ∑ j, (A (stdOrthonormalBasis ℝ E k) i * B (stdOrthonormalBasis ℝ E k) j) *
        H (Pi.single i 1) (Pi.single j 1) :=
      Finset.sum_congr rfl (fun k _ => bilinear_coordinate_expansion H _ _)
    _ = _ := ?_
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [coordinateCovariance, Finset.sum_mul]

theorem gaussian_comparison_entrywise {f : (I → ℝ) → ℝ} {b c : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith b f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (c : ℝ))
    (A B : E →L[ℝ] (I → ℝ))
    (hcross : ∀ i j, coordinateCovariance E A B i j = 0)
    (hentry : ∀ x i j, 0 ≤ (coordinateCovariance E A A i j - coordinateCovariance E B B i j) *
      fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)) :
    linearGaussianExpectation E f B ≤ linearGaussianExpectation E f A := by
  apply gaussian_comparison E hf hLip hH A B
  · intro x
    rw [bilinear_covariance_trace]
    simp only [hcross, zero_mul, Finset.sum_const_zero]
  · intro x
    rw [bilinear_covariance_trace]
    simp only [coordinateCovariance_swap E B A, hcross, zero_mul, Finset.sum_const_zero]
  · intro x
    rw [bilinear_covariance_trace, bilinear_covariance_trace]
    apply sub_nonneg.mp
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_nonneg
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_nonneg
    intro j _
    simpa only [sub_mul] using hentry x i j

end GradientHessian.GaussianConcentration
