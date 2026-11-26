import HeavyTail.GaussianWeighted
import Mathlib.MeasureTheory.Integral.Prod

/-! Product-law integration of the Gaussian quadratic term against genuine
noise. This is the total-second-moment bridge for `lem:mixed-exp`.
The eventual full mixed-exponential lemma must require `η ≥ 0`: the source
omits this hypothesis, although its tuning makes `η` strictly positive.
-/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace HeavyTail.GaussianEstimates

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussian_noise_weighted_integrable {ξ : Ω → E} (hξ : Measurable ξ)
    (h2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) P) (b : E) (c : ℝ) :
    Integrable (fun w : Ω × E => Real.exp (c * |⟪b, w.2⟫_ℝ|) * ⟪ξ w.1, w.2⟫_ℝ ^ 2)
      (P.prod (euclideanGaussianLaw E)) := by
  let F : Ω × E → ℝ := fun w => Real.exp (c * |⟪b, w.2⟫_ℝ|) * ⟪ξ w.1, w.2⟫_ℝ ^ 2
  have hf : StronglyMeasurable F := by
    apply Measurable.stronglyMeasurable
    dsimp [F]
    fun_prop
  apply (integrable_prod_iff hf.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun ω => gaussian_weighted_square_integrable E b (ξ ω) c
  · have hi := (h2.const_mul (Real.exp (2 * c ^ 2 * ‖b‖ ^ 2) + 3 / 2))
    apply hi.mono' hf.norm.integral_prod_right'.aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      have hnonneg : 0 ≤ ∫ z, ‖F (ω, z)‖ ∂euclideanGaussianLaw E :=
        integral_nonneg fun z => norm_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      have he : (fun z => ‖F (ω, z)‖) =
          fun z => Real.exp (c * |⟪b, z⟫_ℝ|) * ⟪ξ ω, z⟫_ℝ ^ 2 := by
        funext z
        dsimp [F]
        exact abs_of_nonneg (by positivity)
      rw [he]
      exact gaussian_weighted_square_bound E b (ξ ω) c

theorem gaussian_noise_weighted_bound {ξ : Ω → E} (hξ : Measurable ξ)
    (h2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) P) (b : E) (c : ℝ) :
    (∫ w : Ω × E, Real.exp (c * |⟪b, w.2⟫_ℝ|) * ⟪ξ w.1, w.2⟫_ℝ ^ 2
      ∂P.prod (euclideanGaussianLaw E)) ≤
      (Real.exp (2 * c ^ 2 * ‖b‖ ^ 2) + 3 / 2) * (∫ ω, ‖ξ ω‖ ^ 2 ∂P) := by
  have hi := gaussian_noise_weighted_integrable E hξ h2 b c
  rw [integral_prod _ hi]
  have h := integral_mono hi.integral_prod_left
    (h2.const_mul (Real.exp (2 * c ^ 2 * ‖b‖ ^ 2) + 3 / 2))
    (fun ω => gaussian_weighted_square_bound E b (ξ ω) c)
  rw [integral_const_mul] at h
  exact h

theorem gaussian_noise_second_identity {ξ : Ω → E} (hξ : Measurable ξ)
    (h2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) P) :
    (∫ w : Ω × E, ⟪ξ w.1, w.2⟫_ℝ ^ 2 ∂P.prod (euclideanGaussianLaw E)) =
      ∫ ω, ‖ξ ω‖ ^ 2 ∂P := by
  have hi := gaussian_noise_weighted_integrable E hξ h2 (0 : E) 0
  simp only [zero_mul, Real.exp_zero, one_mul] at hi
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => gaussian_inner_second E (ξ ω)

theorem gaussian_noise_weak_integrable {ξ : Ω → E} {p : ℝ} (b v : E) (c : ℝ)
    (hpint : Integrable (fun ω => |⟪v, ξ ω⟫_ℝ| ^ p) P) :
    Integrable (fun w : Ω × E => Real.exp (c * |⟪b, w.2⟫_ℝ|) * |⟪v, ξ w.1⟫_ℝ| ^ p)
      (P.prod (euclideanGaussianLaw E)) := by
  simpa only [mul_comm] using hpint.mul_prod (gaussian_exp_abs_inner_integrable E b c)

theorem gaussian_noise_weak_bound {ξ : Ω → E} {p : ℝ} (b v : E) (c : ℝ) :
    (∫ w : Ω × E, Real.exp (c * |⟪b, w.2⟫_ℝ|) * |⟪v, ξ w.1⟫_ℝ| ^ p
      ∂P.prod (euclideanGaussianLaw E)) ≤
      2 * Real.exp (c ^ 2 * ‖b‖ ^ 2 / 2) * (∫ ω, |⟪v, ξ ω⟫_ℝ| ^ p ∂P) := by
  have he : (∫ w : Ω × E, Real.exp (c * |⟪b, w.2⟫_ℝ|) * |⟪v, ξ w.1⟫_ℝ| ^ p
      ∂P.prod (euclideanGaussianLaw E)) =
      (∫ ω, |⟪v, ξ ω⟫_ℝ| ^ p ∂P) *
        (∫ z, Real.exp (c * |⟪b, z⟫_ℝ|) ∂euclideanGaussianLaw E) := by
    simpa only [mul_comm] using integral_prod_mul
      (μ := P) (ν := euclideanGaussianLaw E) (fun ω => |⟪v, ξ ω⟫_ℝ| ^ p)
      (fun z => Real.exp (c * |⟪b, z⟫_ℝ|))
  rw [he, mul_comm]
  exact mul_le_mul_of_nonneg_right (gaussian_exp_abs_inner_bound E b c)
    (integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _)

end HeavyTail.GaussianEstimates
