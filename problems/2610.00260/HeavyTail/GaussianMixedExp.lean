import HeavyTail.GaussianMixedAssembly
import Mathlib.MeasureTheory.Function.L2Space

/-!
The positive-learning-rate Gaussian mixed-exponential bridge.
The source's standalone `lem:mixed-exp` omits `η ≥ 0`; its algorithmic tuning
does imply positivity. This file keeps that condition explicit and does not
change the source manuscript.
-/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace HeavyTail.GaussianEstimates

def mixedWeakConstant : ℝ := 2 * Real.exp (1 / 4) * Real.exp 2
def mixedQuadraticConstant : ℝ := Real.exp (1 / 4) * (Real.exp 2 + 3 / 2)

theorem shifted_exp_le {t₀ : ℝ} (ht : |t₀| ≤ 1 / 8) (y : ℝ) :
    Real.exp (2 * |t₀ + y|) ≤ Real.exp (1 / 4) * Real.exp (2 * |y|) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := abs_add_le t₀ y
  linarith

theorem clipped_exp_le (t u v ε : ℝ) (hε : ε = -1 ∨ ε = 1) :
    Real.exp (ε * (HeavyTail.clip (t + u + v) - t)) ≤ Real.exp (1 + |t|) := by
  apply Real.exp_le_exp.mpr
  have hc := HeavyTail.clip_mem (t + u + v)
  rcases hε with rfl | rfl <;> nlinarith [le_abs_self t, neg_le_abs t]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem noise_integrable_of_second {ξ : Ω → E} (hξ : Measurable ξ)
    (h2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) P) : Integrable ξ P := by
  apply ((integrable_const (1 : ℝ)).add h2).mono' hξ.aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    simp only [Pi.add_apply]
    have := sq_nonneg (‖ξ ω‖ - 1)
    nlinarith

theorem noise_gaussian_linear_integrable {ξ : Ω → E} (hξ : Measurable ξ)
    (h2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) P) :
    Integrable (fun w : Ω × E => ⟪ξ w.1, w.2⟫_ℝ) (P.prod (euclideanGaussianLaw E)) := by
  have hsq := gaussian_noise_weighted_integrable E hξ h2 (0 : E) 0
  simp only [zero_mul, Real.exp_zero, one_mul] at hsq
  apply ((integrable_const (1 : ℝ)).add hsq).mono'
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · exact ae_of_all _ fun w => by
      simp only [Pi.add_apply]
      rw [Real.norm_eq_abs]
      nlinarith [sq_nonneg (|⟪ξ w.1, w.2⟫_ℝ| - 1), sq_abs ⟪ξ w.1, w.2⟫_ℝ]

theorem noise_gaussian_linear_zero {ξ : Ω → E} (hξ : Measurable ξ)
    (h2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) P) :
    (∫ w : Ω × E, ⟪ξ w.1, w.2⟫_ℝ ∂P.prod (euclideanGaussianLaw E)) = 0 := by
  rw [integral_prod _ (noise_gaussian_linear_integrable E hξ h2)]
  simp_rw [gaussian_inner_mean_zero]
  simp

theorem shifted_weak_product {ξ : Ω → E} {p t₀ : ℝ} (ht : |t₀| ≤ 1 / 8)
    (d v₀ : E) (hd : 4 * ‖d‖ ^ 2 ≤ 1)
    (hpint : Integrable (fun ω => |⟪v₀, ξ ω⟫_ℝ| ^ p) P) :
    Integrable (fun w : Ω × E => Real.exp (2 * |t₀ + ⟪d, w.2⟫_ℝ|) *
      |⟪v₀, ξ w.1⟫_ℝ| ^ p) (P.prod (euclideanGaussianLaw E)) ∧
    (∫ w : Ω × E, Real.exp (2 * |t₀ + ⟪d, w.2⟫_ℝ|) * |⟪v₀, ξ w.1⟫_ℝ| ^ p
      ∂P.prod (euclideanGaussianLaw E)) ≤
      mixedWeakConstant * (∫ ω, |⟪v₀, ξ ω⟫_ℝ| ^ p ∂P) := by
  have hdom := (gaussian_noise_weak_integrable E d v₀ 2 hpint).const_mul (Real.exp (1 / 4))
  have hpoint (w : Ω × E) : Real.exp (2 * |t₀ + ⟪d, w.2⟫_ℝ|) * |⟪v₀, ξ w.1⟫_ℝ| ^ p ≤
      Real.exp (1 / 4) * (Real.exp (2 * |⟪d, w.2⟫_ℝ|) * |⟪v₀, ξ w.1⟫_ℝ| ^ p) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (shifted_exp_le ht ⟪d, w.2⟫_ℝ)
      (Real.rpow_nonneg (abs_nonneg _) p)
  have hi : Integrable (fun w : Ω × E => Real.exp (2 * |t₀ + ⟪d, w.2⟫_ℝ|) *
      |⟪v₀, ξ w.1⟫_ℝ| ^ p) (P.prod (euclideanGaussianLaw E)) := by
    have hweight : Integrable (fun z : E => Real.exp (2 * |t₀ + ⟪d, z⟫_ℝ|))
        (euclideanGaussianLaw E) := by
      apply ((gaussian_exp_abs_inner_integrable E d 2).const_mul (Real.exp (1 / 4))).mono'
      · exact Continuous.aestronglyMeasurable (by fun_prop)
      · exact ae_of_all _ fun z => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact shifted_exp_le ht _
    simpa only [mul_comm] using hpint.mul_prod hweight
  refine ⟨hi, ?_⟩
  have h := integral_mono hi hdom hpoint
  rw [integral_const_mul] at h
  have hb := gaussian_noise_weak_bound (P := P) (ξ := ξ) (p := p) E d v₀ 2
  have he : Real.exp ((2 : ℝ) ^ 2 * ‖d‖ ^ 2 / 2) ≤ Real.exp 2 :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ‖d‖])
  have hnonneg : 0 ≤ ∫ ω, |⟪v₀, ξ ω⟫_ℝ| ^ p ∂P :=
    integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have hbound := hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2)) hnonneg)
  have hh := h.trans (mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le)
  simpa only [mixedWeakConstant, mul_assoc, mul_left_comm] using hh

theorem shifted_quadratic_product {ξ : Ω → E} (hξ : Measurable ξ)
    (h2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) P) {t₀ : ℝ} (ht : |t₀| ≤ 1 / 8)
    (d : E) (hd : 4 * ‖d‖ ^ 2 ≤ 1) (a : ℝ) :
    Integrable (fun w : Ω × E => Real.exp (2 * |t₀ + ⟪d, w.2⟫_ℝ|) *
      (a * ⟪ξ w.1, w.2⟫_ℝ) ^ 2) (P.prod (euclideanGaussianLaw E)) ∧
    (∫ w : Ω × E, Real.exp (2 * |t₀ + ⟪d, w.2⟫_ℝ|) * (a * ⟪ξ w.1, w.2⟫_ℝ) ^ 2
      ∂P.prod (euclideanGaussianLaw E)) ≤
      mixedQuadraticConstant * a ^ 2 * (∫ ω, ‖ξ ω‖ ^ 2 ∂P) := by
  have hdom := (gaussian_noise_weighted_integrable E hξ h2 d 2).const_mul
    (Real.exp (1 / 4) * a ^ 2)
  have hpoint (w : Ω × E) : Real.exp (2 * |t₀ + ⟪d, w.2⟫_ℝ|) * (a * ⟪ξ w.1, w.2⟫_ℝ) ^ 2 ≤
      (Real.exp (1 / 4) * a ^ 2) * (Real.exp (2 * |⟪d, w.2⟫_ℝ|) * ⟪ξ w.1, w.2⟫_ℝ ^ 2) := by
    have h := mul_le_mul_of_nonneg_right (shifted_exp_le ht ⟪d, w.2⟫_ℝ)
      (sq_nonneg (a * ⟪ξ w.1, w.2⟫_ℝ))
    nlinarith
  have hi : Integrable (fun w : Ω × E => Real.exp (2 * |t₀ + ⟪d, w.2⟫_ℝ|) *
      (a * ⟪ξ w.1, w.2⟫_ℝ) ^ 2) (P.prod (euclideanGaussianLaw E)) := by
    apply hdom.mono'
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · exact ae_of_all _ fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hpoint w
  refine ⟨hi, ?_⟩
  have h := integral_mono hi hdom hpoint
  rw [integral_const_mul] at h
  have hb := gaussian_noise_weighted_bound E hξ h2 d 2
  have he : Real.exp (2 * (2 : ℝ) ^ 2 * ‖d‖ ^ 2) ≤ Real.exp 2 :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hn : 0 ≤ ∫ ω, ‖ξ ω‖ ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have hb' := hb.trans (mul_le_mul_of_nonneg_right (add_le_add_right he _) hn)
  have hh := h.trans (mul_le_mul_of_nonneg_left hb' (by positivity))
  unfold mixedQuadraticConstant
  convert hh using 1 <;> ring

theorem shifted_tail_product {t₀ : ℝ} (ht : |t₀| ≤ 1 / 8) (d : E)
    (hd : 4 * ‖d‖ ^ 2 ≤ 1) :
    Integrable (fun w : Ω × E => shiftedTail t₀ ⟪d, w.2⟫_ℝ) (P.prod (euclideanGaussianLaw E)) ∧
    (∫ w : Ω × E, shiftedTail t₀ ⟪d, w.2⟫_ℝ ∂P.prod (euclideanGaussianLaw E)) ≤
      4 * mixedQuadraticConstant * ‖d‖ ^ 2 := by
  constructor
  · simpa only [one_mul] using (integrable_const (1 : ℝ) (μ := P)).mul_prod
      (shiftedTail_integrable E ht d)
  · have he : (∫ w : Ω × E, shiftedTail t₀ ⟪d, w.2⟫_ℝ ∂P.prod (euclideanGaussianLaw E)) =
        ∫ z, shiftedTail t₀ ⟪d, z⟫_ℝ ∂euclideanGaussianLaw E := by
      simpa using integral_prod_mul (μ := P) (ν := euclideanGaussianLaw E)
        (fun _ : Ω => (1 : ℝ)) (fun z => shiftedTail t₀ ⟪d, z⟫_ℝ)
    rw [he]
    convert gaussian_shifted_tail_bound E ht d hd using 1 <;> unfold mixedQuadraticConstant <;> ring

end HeavyTail.GaussianEstimates
