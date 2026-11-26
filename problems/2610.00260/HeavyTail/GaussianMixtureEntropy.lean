import HeavyTail.MixtureEnvelopes
import HeavyTail.GaussianDirections

/-!
# Entropy regularity for Gaussian exponential densities

Components are explicit normalized exponential-linear densities relative to the
concrete standard Euclidean Gaussian. No entropy regularity hypothesis is left
to the caller. A bridge identifying each density measure with the translated
Gaussian pushforward is separate from the results in this file.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators InnerProductSpace

namespace HeavyTail

theorem exp_mul_abs_le_pair (x y : ℝ) :
    Real.exp x * |y| ≤ Real.exp (x + y) + Real.exp (x - y) := by
  have hy : |y| ≤ Real.exp y + Real.exp (-y) := by
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy]
      linarith [Real.add_one_le_exp y, Real.exp_pos (-y)]
    · rw [abs_of_neg (lt_of_not_ge hy)]
      linarith [Real.add_one_le_exp (-y), Real.exp_pos y]
  have h := mul_le_mul_of_nonneg_left hy (Real.exp_pos x).le
  simpa only [mul_add, ← Real.exp_add, sub_eq_add_neg] using h

theorem integrable_exp_mul_abs_of_pair {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hp : Integrable (fun ω => Real.exp (f ω + g ω)) μ)
    (hm : Integrable (fun ω => Real.exp (f ω - g ω)) μ) :
    Integrable (fun ω => Real.exp (f ω) * |g ω|) μ := by
  apply (hp.add hm).mono' ((hf.exp.mul hg.abs).aestronglyMeasurable)
  filter_upwards with ω
  simpa only [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _)] using
    exp_mul_abs_le_pair (f ω) (g ω)

theorem entropyEnvelope_integrable_of_exponential_pairs
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {μ : Measure Ω} {r : ι → Ω → ℝ}
    (hr : ∀ i, Measurable (r i)) (h0 : ∀ i, Integrable (fun ω => Real.exp (r i ω)) μ)
    (hp : ∀ i j, Integrable (fun ω => Real.exp (r i ω + r j ω)) μ)
    (hm : ∀ i j, Integrable (fun ω => Real.exp (r i ω - r j ω)) μ) :
    Integrable (entropyEnvelope r) μ := by
  have hi (i : ι) : Integrable (fun ω => Real.exp (r i ω) * (1 + ∑ j, |r j ω|)) μ := by
    have hsum := integrable_finset_sum Finset.univ (fun j _ =>
      integrable_exp_mul_abs_of_pair (hr i) (hr j) (hp i j) (hm i j))
    convert (h0 i).add hsum using 1
    funext ω
    simp only [Pi.add_apply, mul_add, mul_one, Finset.mul_sum]
  convert integrable_finset_sum Finset.univ (fun i _ => hi i) using 1
  funext ω
  simp only [entropyEnvelope, logEnvelope, densityEnvelope, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

namespace GaussianEntropy

open GaussianEstimates

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def gaussianLogDensity (t : E) (z : E) : ℝ := ⟪t, z⟫_ℝ - ‖t‖ ^ 2 / 2
def gaussianExponentialDensity (t : E) (z : E) : ℝ := Real.exp (gaussianLogDensity E t z)

omit [FiniteDimensional ℝ E] in
theorem gaussianLogDensity_measurable (t : E) : Measurable (gaussianLogDensity E t) := by
  unfold gaussianLogDensity
  fun_prop

theorem gaussian_affine_exp_integrable (t : E) (c : ℝ) :
    Integrable (fun z => Real.exp (⟪t, z⟫_ℝ + c)) (euclideanGaussianLaw E) := by
  have h := (gaussian_inner_exp_integrable E t 1).mul_const (Real.exp c)
  simpa only [one_mul, Real.exp_add] using h

theorem gaussianExponentialDensity_integrable (t : E) :
    Integrable (gaussianExponentialDensity E t) (euclideanGaussianLaw E) := by
  exact gaussian_affine_exp_integrable E t (-(‖t‖ ^ 2 / 2))

theorem gaussianExponentialDensity_normalized (t : E) :
    (∫ z, gaussianExponentialDensity E t z ∂euclideanGaussianLaw E) = 1 := by
  simp only [gaussianExponentialDensity, gaussianLogDensity, Real.exp_sub]
  rw [integral_div, gaussian_exp_inner E, div_self (Real.exp_ne_zero _)]

theorem gaussianLogDensity_pair_integrable (t u : E) :
    Integrable (fun z => Real.exp (gaussianLogDensity E t z + gaussianLogDensity E u z))
      (euclideanGaussianLaw E) ∧
    Integrable (fun z => Real.exp (gaussianLogDensity E t z - gaussianLogDensity E u z))
      (euclideanGaussianLaw E) := by
  constructor
  · convert gaussian_affine_exp_integrable E (t + u) (-‖t‖ ^ 2 / 2 - ‖u‖ ^ 2 / 2) using 1
    funext z
    congr 1
    simp only [gaussianLogDensity, inner_add_left]
    ring
  · convert gaussian_affine_exp_integrable E (t - u) (-‖t‖ ^ 2 / 2 + ‖u‖ ^ 2 / 2) using 1
    funext z
    congr 1
    simp only [gaussianLogDensity, inner_sub_left]
    ring

theorem gaussian_entropyEnvelope_integrable {ι : Type*} [Fintype ι] (t : ι → E) :
    Integrable (entropyEnvelope (fun i => gaussianLogDensity E (t i))) (euclideanGaussianLaw E) :=
  entropyEnvelope_integrable_of_exponential_pairs
    (fun i => gaussianLogDensity_measurable E (t i))
    (fun i => gaussianExponentialDensity_integrable E (t i))
    (fun i j => (gaussianLogDensity_pair_integrable E (t i) (t j)).1)
    (fun i j => (gaussianLogDensity_pair_integrable E (t i) (t j)).2)

theorem gaussian_mixture_entropy_regular {ι : Type*} [Fintype ι]
    (t : ι → E) {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) :
    Integrable (mixtureEntropyIntegrand (fun i => gaussianExponentialDensity E (t i)) w)
      (euclideanGaussianLaw E) ∧
    Integrable (mixtureEntropyDifferential (fun i => gaussianExponentialDensity E (t i)) w)
      (euclideanGaussianLaw E) :=
  exponential_entropy_regular (fun i => gaussianLogDensity_measurable E (t i))
    (gaussian_entropyEnvelope_integrable E t) hw

theorem gaussian_mixture_entropy_derivative {ι : Type*} [Fintype ι]
    (t : ι → E) {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) :
    HasFDerivWithinAt
      (mixtureEntropy (euclideanGaussianLaw E) (fun i => gaussianExponentialDensity E (t i)))
      (mixtureEntropyDerivative (euclideanGaussianLaw E) (fun i => gaussianExponentialDensity E (t i)) w)
      (stdSimplex ℝ ι) w := by
  apply mixtureEntropy_hasFDerivWithinAt (fun i z => Real.exp_pos _) hw
    (fun v hv => (gaussian_mixture_entropy_regular E t hv).1)
    (gaussian_mixture_entropy_regular E t hw).2 (gaussian_entropyEnvelope_integrable E t)
    (entropyEnvelope_nonneg _)
  exact ae_of_all _ (fun z v hv => exponential_entropy_difference_bound _ hv hw z)

theorem gaussian_mixture_mirror_optimizer_exists {ι : Type*} [Fintype ι] [Nonempty ι]
    (t : ι → E) (L : (ι → ℝ) →L[ℝ] ℝ) (x : ι → ℝ) :
    ∃ y ∈ stdSimplex ℝ ι, IsMinOn
      (fun z => L z + bregmanDivergence
        (mixtureEntropy (euclideanGaussianLaw E) (fun i => gaussianExponentialDensity E (t i)))
        (mixtureEntropyDerivative (euclideanGaussianLaw E) (fun i => gaussianExponentialDensity E (t i))) z x)
      (stdSimplex ℝ ι) y := by
  apply exists_mixtureEntropy_mirror_minimizer (fun i z => Real.exp_pos _)
    (fun w hw => (gaussian_mixture_entropy_regular E t hw).1)
    (fun w hw => (gaussian_mixture_entropy_regular E t hw).2) _ L x
  intro w hw
  exact ⟨entropyEnvelope _, gaussian_entropyEnvelope_integrable E t,
    entropyEnvelope_nonneg _, ae_of_all _ (fun z v hv => exponential_entropy_difference_bound _ hv hw z)⟩

theorem gaussian_weighted_self_first_moment (t : E) :
    (∫ z, ⟪t, z⟫_ℝ * Real.exp ⟪t, z⟫_ℝ ∂euclideanGaussianLaw E) =
      Real.exp (‖t‖ ^ 2 / 2) * ‖t‖ ^ 2 := by
  have hd := hasDerivAt_mgf (gaussian_inner_exp_interior E t 1)
  have he : mgf (fun z => ⟪t, z⟫_ℝ) (euclideanGaussianLaw E) =
      (fun s => Real.exp (s ^ 2 * ‖t‖ ^ 2 / 2)) := funext (gaussian_inner_mgf E t)
  rw [he] at hd
  have hcalc : HasDerivAt (fun s : ℝ => Real.exp (s ^ 2 * ‖t‖ ^ 2 / 2))
      (Real.exp (‖t‖ ^ 2 / 2) * ‖t‖ ^ 2) 1 := by
    convert ((((hasDerivAt_id (1 : ℝ)).pow 2).mul_const (‖t‖ ^ 2)).div_const 2).exp using 1
    norm_num
  simpa only [one_mul] using hd.unique hcalc

theorem gaussian_density_entropy (t : E) :
    (∫ z, gaussianExponentialDensity E t z * Real.log (gaussianExponentialDensity E t z)
      ∂euclideanGaussianLaw E) = ‖t‖ ^ 2 / 2 := by
  have h1 : Integrable (fun z => ⟪t, z⟫_ℝ * Real.exp ⟪t, z⟫_ℝ) (euclideanGaussianLaw E) := by
    simpa only [pow_one, one_mul] using
      integrable_pow_mul_exp_of_mem_interior_integrableExpSet (gaussian_inner_exp_interior E t 1) 1
  have h0 : Integrable (fun z => Real.exp ⟪t, z⟫_ℝ) (euclideanGaussianLaw E) := by
    simpa only [one_mul] using gaussian_inner_exp_integrable E t 1
  have heq : (fun z => gaussianExponentialDensity E t z * Real.log (gaussianExponentialDensity E t z)) =
      (fun z => Real.exp (-(‖t‖ ^ 2 / 2)) *
        (⟪t, z⟫_ℝ * Real.exp ⟪t, z⟫_ℝ - (‖t‖ ^ 2 / 2) * Real.exp ⟪t, z⟫_ℝ)) := by
    funext z
    simp only [gaussianExponentialDensity, Real.log_exp]
    simp only [gaussianLogDensity, Real.exp_sub, Real.exp_neg]
    ring
  rw [heq, integral_const_mul, integral_sub h1 (h0.const_mul (‖t‖ ^ 2 / 2)),
    integral_const_mul, gaussian_weighted_self_first_moment E, gaussian_exp_inner E, Real.exp_neg]
  field_simp
  ring

/-- Exact Gaussian comparator cost relative to the initial reference density. -/
theorem gaussian_comparator_KL (u c : E) (a : ℝ) :
    densityRelativeEntropy (euclideanGaussianLaw E)
      (gaussianExponentialDensity E (a⁻¹ • (u - c))) (fun _ => 1) = ‖u - c‖ ^ 2 / (2 * a ^ 2) := by
  simp only [densityRelativeEntropy, div_one]
  rw [gaussian_density_entropy E, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem gaussian_comparator_KL_bound (u c : E) {a R : ℝ}
    (hR : 0 ≤ R) (huc : ‖u - c‖ ≤ R) :
    densityRelativeEntropy (euclideanGaussianLaw E)
      (gaussianExponentialDensity E (a⁻¹ • (u - c))) (fun _ => 1) ≤ R ^ 2 / (2 * a ^ 2) := by
  rw [gaussian_comparator_KL E]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [norm_nonneg (u - c)]

end GaussianEntropy
end HeavyTail
