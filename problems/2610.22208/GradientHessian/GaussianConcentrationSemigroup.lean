import GradientHessian.GaussianConcentrationIntegrability
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual Gaussian mixing and invariance of the Mehler operator.  These are
the measure-theoretic foundations of the source Ornstein--Uhlenbeck proof. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory ProbabilityTheory GaussianHilbert
open scoped InnerProductSpace

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussian_mixing {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    ((euclideanGaussianLaw E).prod (euclideanGaussianLaw E)).map
      (fun z : E × E => a • z.1 + b • z.2) = euclideanGaussianLaw E := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply,
    integral_map_of_stronglyMeasurable (by fun_prop)
      ((by fun_prop : Continuous (fun x : E => Complex.exp ((⟪x, t⟫_ℝ : ℂ) * Complex.I))).stronglyMeasurable)]
  have he (z : E × E) :
      Complex.exp ((⟪a • z.1 + b • z.2, t⟫_ℝ : ℂ) * Complex.I) =
        Complex.exp ((⟪z.1, a • t⟫_ℝ : ℂ) * Complex.I) *
          Complex.exp ((⟪z.2, b • t⟫_ℝ : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [inner_add_left, real_inner_smul_left, inner_smul_right,
      Complex.ofReal_add, Complex.ofReal_mul]
    ring
  simp_rw [he]
  rw [integral_prod_mul (fun x : E => Complex.exp ((⟪x, a • t⟫_ℝ : ℂ) * Complex.I))
    (fun y : E => Complex.exp ((⟪y, b • t⟫_ℝ : ℂ) * Complex.I))]
  change charFun (euclideanGaussianLaw E) (a • t) *
    charFun (euclideanGaussianLaw E) (b • t) = charFun (euclideanGaussianLaw E) t
  rw [euclideanGaussian_characteristic, euclideanGaussian_characteristic,
    euclideanGaussian_characteristic, ← Complex.exp_add]
  have hn (c : ℝ) : (‖c • t‖ : ℂ) ^ 2 = (c : ℂ) ^ 2 * (‖t‖ : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    push_cast
    rfl
  rw [hn a, hn b]
  have hab' : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by exact_mod_cast hab
  congr 1
  calc
    -((a : ℂ) ^ 2 * (‖t‖ : ℂ) ^ 2) / 2 + -((b : ℂ) ^ 2 * (‖t‖ : ℂ) ^ 2) / 2 =
        -((a : ℂ) ^ 2 + (b : ℂ) ^ 2) * (‖t‖ : ℂ) ^ 2 / 2 := by ring
    _ = _ := by rw [hab']; ring

def mehler (ρ : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  ∫ z, f (ρ • x + Real.sqrt (1 - ρ ^ 2) • z) ∂euclideanGaussianLaw E

theorem mehler_invariant {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) {f : E → ℝ}
    (hf : Integrable f (euclideanGaussianLaw E)) :
    (∫ x, mehler E ρ f x ∂euclideanGaussianLaw E) = ∫ x, f x ∂euclideanGaussianLaw E := by
  have hm := gaussian_mixing E (a := ρ) (b := Real.sqrt (1 - ρ ^ 2)) (by
    rw [Real.sq_sqrt (sub_nonneg.mpr hρ)]
    ring)
  have hmmeas : Measurable (fun z : E × E => ρ • z.1 + Real.sqrt (1 - ρ ^ 2) • z.2) := by
    fun_prop
  have hi : Integrable (fun z : E × E => f (ρ • z.1 + Real.sqrt (1 - ρ ^ 2) • z.2))
      ((euclideanGaussianLaw E).prod (euclideanGaussianLaw E)) := by
    have hmap : Integrable f (((euclideanGaussianLaw E).prod (euclideanGaussianLaw E)).map
        (fun z : E × E => ρ • z.1 + Real.sqrt (1 - ρ ^ 2) • z.2)) := by
      rw [hm]
      exact hf
    exact (integrable_map_measure hmap.aestronglyMeasurable hmmeas.aemeasurable).mp hmap
  change (∫ x, ∫ z, f (ρ • x + Real.sqrt (1 - ρ ^ 2) • z) ∂euclideanGaussianLaw E
    ∂euclideanGaussianLaw E) = _
  rw [← integral_prod _ hi]
  have hmapmeas : AEStronglyMeasurable f
      (((euclideanGaussianLaw E).prod (euclideanGaussianLaw E)).map
        (fun z : E × E => ρ • z.1 + Real.sqrt (1 - ρ ^ 2) • z.2)) := by
    rw [hm]
    exact hf.aestronglyMeasurable
  rw [← integral_map hmmeas.aemeasurable hmapmeas, hm]

def ornsteinUhlenbeck (t : ℝ) (f : E → ℝ) : E → ℝ := mehler E (Real.exp (-t)) f

theorem ornsteinUhlenbeck_invariant {t : ℝ} (ht : 0 ≤ t) {f : E → ℝ}
    (hf : Integrable f (euclideanGaussianLaw E)) :
    (∫ x, ornsteinUhlenbeck E t f x ∂euclideanGaussianLaw E) =
      ∫ x, f x ∂euclideanGaussianLaw E := by
  apply mehler_invariant E _ hf
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  nlinarith [Real.exp_pos (-t)]

end GradientHessian.GaussianConcentration
