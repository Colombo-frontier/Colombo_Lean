import GradientHessian.GaussianLipschitzMGF
import Mathlib.Probability.Moments.SubGaussian

/-! Sharp one-sided and two-sided concentration for every Lipschitz
function of the actual standard Gaussian vector. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory ProbabilityTheory GaussianHilbert Set
open scoped NNReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussian_lipschitz_hasSubgaussianMGF {f : E → ℝ} {B : ℝ≥0}
    (hLip : LipschitzWith B f) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂euclideanGaussianLaw E) (B ^ 2)
      (euclideanGaussianLaw E) where
  integrable_exp_mul t := lipschitz_centered_exponential_integrable hLip t
  mgf_le t := by
    have h := gaussian_lipschitz_centered_mgf E hLip t
    simpa only [NNReal.coe_pow, mul_comm ((B : ℝ) ^ 2) (t ^ 2)] using h

theorem gaussian_lipschitz_right_tail {f : E → ℝ} {B : ℝ≥0}
    (hLip : LipschitzWith B f) {t : ℝ} (ht : 0 ≤ t) :
    (euclideanGaussianLaw E).real {x | t ≤ f x - ∫ y, f y ∂euclideanGaussianLaw E} ≤
      Real.exp (-t ^ 2 / (2 * (B : ℝ) ^ 2)) := by
  simpa only [NNReal.coe_pow] using (gaussian_lipschitz_hasSubgaussianMGF E hLip).measure_ge_le ht

theorem gaussian_lipschitz_two_sided_tail {f : E → ℝ} {B : ℝ≥0}
    (hLip : LipschitzWith B f) {t : ℝ} (ht : 0 ≤ t) :
    (euclideanGaussianLaw E).real {x | t ≤ |f x - ∫ y, f y ∂euclideanGaussianLaw E|} ≤
      2 * Real.exp (-t ^ 2 / (2 * (B : ℝ) ^ 2)) := by
  have hp := gaussian_lipschitz_right_tail E hLip ht
  have hn := gaussian_lipschitz_right_tail E hLip.neg ht
  simp only [Pi.neg_apply] at hn
  have he (x : E) : -f x - (∫ y, -f y ∂euclideanGaussianLaw E) =
      -(f x - ∫ y, f y ∂euclideanGaussianLaw E) := by rw [integral_neg]; ring
  have hs : {x : E | t ≤ |f x - ∫ y, f y ∂euclideanGaussianLaw E|} ⊆
      {x | t ≤ f x - ∫ y, f y ∂euclideanGaussianLaw E} ∪
      {x | t ≤ -f x - ∫ y, -f y ∂euclideanGaussianLaw E} := by
    intro x hx
    change t ≤ |f x - ∫ y, f y ∂euclideanGaussianLaw E| at hx
    rcases le_abs.mp hx with h | h
    · exact Or.inl h
    · apply Or.inr
      change t ≤ -f x - ∫ y, -f y ∂euclideanGaussianLaw E
      rw [he]
      exact h
  calc
    _ ≤ (euclideanGaussianLaw E).real
        ({x | t ≤ f x - ∫ y, f y ∂euclideanGaussianLaw E} ∪
         {x | t ≤ -f x - ∫ y, -f y ∂euclideanGaussianLaw E}) := measureReal_mono hs
    _ ≤ (euclideanGaussianLaw E).real {x | t ≤ f x - ∫ y, f y ∂euclideanGaussianLaw E} +
        (euclideanGaussianLaw E).real {x | t ≤ -f x - ∫ y, -f y ∂euclideanGaussianLaw E} :=
      measureReal_union_le _ _
    _ ≤ _ := by linarith only [hp, hn]

theorem gaussian_lipschitz_concentration {f : E → ℝ} {B : ℝ≥0}
    (hLip : LipschitzWith B f) :
    (∀ t : ℝ, (∫ x, Real.exp (t * (f x - ∫ y, f y ∂euclideanGaussianLaw E))
      ∂euclideanGaussianLaw E) ≤ Real.exp (t ^ 2 * (B : ℝ) ^ 2 / 2)) ∧
    (∀ t : ℝ, 0 ≤ t → (euclideanGaussianLaw E).real
      {x | t ≤ |f x - ∫ y, f y ∂euclideanGaussianLaw E|} ≤
      2 * Real.exp (-t ^ 2 / (2 * (B : ℝ) ^ 2))) :=
  ⟨gaussian_lipschitz_centered_mgf E hLip, fun _ ht => gaussian_lipschitz_two_sided_tail E hLip ht⟩

end GradientHessian.GaussianConcentration
