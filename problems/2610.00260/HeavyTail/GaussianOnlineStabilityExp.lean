import HeavyTail.GaussianOnlineStabilityPullback

/-! Exact exponential-linear Gaussian mixture integrals and deterministic
bounds for the online exponential factor. These bounds are uniform in the
observed vector, so they later certify adapted-process integrability. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace

namespace HeavyTail.GaussianEntropy
open GaussianEstimates

variable {ι : Type*} [Fintype ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem physical_exp_eq_affine (c b x z : E) (a η : ℝ) :
    Real.exp (η * ⟪b, c + a • z - x⟫_ℝ) =
      Real.exp (⟪(η * a) • b, z⟫_ℝ + η * ⟪b, c - x⟫_ℝ) := by
  congr 1
  simp only [inner_add_right, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  ring

theorem gaussian_component_physical_exp_integrable (c center b x : E) (a η : ℝ) :
    Integrable (fun z => gaussianExponentialDensity E (a⁻¹ • (center - c)) z *
      Real.exp (η * ⟪b, c + a • z - x⟫_ℝ)) (euclideanGaussianLaw E) := by
  simp_rw [physical_exp_eq_affine]
  exact gaussian_weighted_affine_exp_integrable E _ _ _

theorem gaussian_component_physical_exp_integral (c center b x : E) {a : ℝ}
    (ha : a ≠ 0) (η : ℝ) :
    (∫ z, gaussianExponentialDensity E (a⁻¹ • (center - c)) z *
      Real.exp (η * ⟪b, c + a • z - x⟫_ℝ) ∂euclideanGaussianLaw E) =
      Real.exp (η * ⟪b, center - x⟫_ℝ + η ^ 2 * a ^ 2 * ‖b‖ ^ 2 / 2) := by
  simp_rw [physical_exp_eq_affine]
  rw [gaussian_weighted_affine_exp_integral]
  congr 1
  simp only [real_inner_smul_left, real_inner_smul_right, inner_sub_right,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp
  <;> ring

theorem physical_mixture_exp_integrable (c b x : E) (a η : ℝ) (centers : ι → E)
    {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) :
    Integrable (fun u => Real.exp (η * ⟪b, u - x⟫_ℝ))
      (physicalGaussianMixtureLaw E c a centers w) := by
  apply (integrable_physicalGaussianMixtureLaw_iff E c a centers hw (by fun_prop)).mpr
  have hi (i : ι) : Integrable (fun z => w i * (gaussianExponentialDensity E (a⁻¹ • (centers i - c)) z *
      Real.exp (η * ⟪b, c + a • z - x⟫_ℝ))) (euclideanGaussianLaw E) :=
    (gaussian_component_physical_exp_integrable E c (centers i) b x a η).const_mul (w i)
  simpa only [physicalMixtureDensity, mixtureDensity_eq_sum, Finset.sum_mul, mul_assoc] using
    integrable_finset_sum Finset.univ (fun i _ => hi i)

theorem physical_mixture_exp_integral (c b x : E) {a : ℝ} (ha : a ≠ 0) (η : ℝ)
    (centers : ι → E) {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) :
    (∫ u, Real.exp (η * ⟪b, u - x⟫_ℝ) ∂physicalGaussianMixtureLaw E c a centers w) =
      ∑ i, w i * Real.exp (η * ⟪b, centers i - x⟫_ℝ + η ^ 2 * a ^ 2 * ‖b‖ ^ 2 / 2) := by
  rw [integral_physicalGaussianMixtureLaw E c a centers hw (by fun_prop)]
  simp_rw [physicalMixtureDensity, mixtureDensity_eq_sum, Finset.sum_mul, mul_assoc]
  have hi (i : ι) : Integrable (fun z => w i * (gaussianExponentialDensity E (a⁻¹ • (centers i - c)) z *
      Real.exp (η * ⟪b, c + a • z - x⟫_ℝ))) (euclideanGaussianLaw E) :=
    (gaussian_component_physical_exp_integrable E c (centers i) b x a η).const_mul (w i)
  rw [integral_finset_sum Finset.univ (fun i _ => hi i)]
  simp only [integral_const_mul, gaussian_component_physical_exp_integral E c _ b x ha η, mul_assoc]

theorem physical_mixture_exp_bound (c b x : E) {a η M R : ℝ} (ha : a ≠ 0)
    (hη : 0 ≤ η) (hM : 0 ≤ M) (hb : ‖b‖ ≤ M)
    (centers : ι → E) (hc : ∀ i, ‖centers i - x‖ ≤ 2 * R)
    {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) :
    (∫ u, Real.exp (η * ⟪b, u - x⟫_ℝ) ∂physicalGaussianMixtureLaw E c a centers w) ≤
      Real.exp (2 * η * M * R + η ^ 2 * a ^ 2 * M ^ 2 / 2) := by
  rw [physical_mixture_exp_integral E c b x ha η centers hw]
  have hterm (i : ι) :
      Real.exp (η * ⟪b, centers i - x⟫_ℝ + η ^ 2 * a ^ 2 * ‖b‖ ^ 2 / 2) ≤
      Real.exp (2 * η * M * R + η ^ 2 * a ^ 2 * M ^ 2 / 2) := by
    apply Real.exp_le_exp.mpr
    have hinner := (real_inner_le_norm b (centers i - x)).trans
      (mul_le_mul hb (hc i) (norm_nonneg _) hM)
    have hlinear := mul_le_mul_of_nonneg_left hinner hη
    have hnorm : ‖b‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg b]
    have hquad := mul_le_mul_of_nonneg_left hnorm (by positivity : 0 ≤ η ^ 2 * a ^ 2 / 2)
    nlinarith only [hlinear, hquad]
  calc
    _ ≤ ∑ i, w i * Real.exp (2 * η * M * R + η ^ 2 * a ^ 2 * M ^ 2 / 2) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hterm i) (hw.1 i))
    _ = _ := by rw [← Finset.sum_mul, hw.2, one_mul]

theorem onlineMixtureError_exp_pointwise (η : ℝ) (Y b x u : E) :
    Real.exp (-onlineMixtureError E η Y b x u) ≤
      Real.exp 1 * Real.exp (η * ⟪b, u - x⟫_ℝ) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  unfold onlineMixtureError
  linarith [(clip_mem (η * ⟪Y, u - x⟫_ℝ)).1]

theorem onlineMixtureError_exp_integrable (c : E) (a η : ℝ) (centers : ι → E)
    {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) (Y b x : E) :
    Integrable (fun u => Real.exp (-onlineMixtureError E η Y b x u))
      (physicalGaussianMixtureLaw E c a centers w) := by
  apply ((physical_mixture_exp_integrable E c b x a η centers hw).const_mul (Real.exp 1)).mono'
  · apply Measurable.aestronglyMeasurable
    unfold onlineMixtureError clip
    fun_prop
  · apply ae_of_all
    intro u
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact onlineMixtureError_exp_pointwise E η Y b x u

def onlineMixtureW (c : E) (a η : ℝ) (centers : ι → E)
    (w : ι → ℝ) (Y b x : E) : ℝ :=
  ∫ u, Real.exp (-onlineMixtureError E η Y b x u) ∂physicalGaussianMixtureLaw E c a centers w

theorem onlineMixtureW_pos (c : E) (a η : ℝ) (centers : ι → E)
    {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) (Y b x : E) :
    0 < onlineMixtureW E c a η centers w Y b x := by
  letI := physicalGaussianMixtureLaw_probability E c a centers hw
  exact integral_exp_pos (onlineMixtureError_exp_integrable E c a η centers hw Y b x)

theorem onlineMixtureW_bound (c b x : E) {a η M R : ℝ} (ha : a ≠ 0)
    (hη : 0 ≤ η) (hM : 0 ≤ M) (hb : ‖b‖ ≤ M)
    (centers : ι → E) (hc : ∀ i, ‖centers i - x‖ ≤ 2 * R)
    {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) (Y : E) :
    onlineMixtureW E c a η centers w Y b x ≤
      Real.exp (1 + 2 * η * M * R + η ^ 2 * a ^ 2 * M ^ 2 / 2) := by
  have h := integral_mono (onlineMixtureError_exp_integrable E c a η centers hw Y b x)
    ((physical_mixture_exp_integrable E c b x a η centers hw).const_mul (Real.exp 1))
    (onlineMixtureError_exp_pointwise E η Y b x)
  rw [integral_const_mul] at h
  change onlineMixtureW E c a η centers w Y b x ≤ _ at h
  have hbound := physical_mixture_exp_bound E c b x ha hη hM hb centers hc hw
  have hmul := mul_le_mul_of_nonneg_left hbound (Real.exp_pos 1).le
  have heq : Real.exp 1 * Real.exp (2 * η * M * R + η ^ 2 * a ^ 2 * M ^ 2 / 2) =
      Real.exp (1 + 2 * η * M * R + η ^ 2 * a ^ 2 * M ^ 2 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  exact h.trans (hmul.trans_eq heq)

end HeavyTail.GaussianEntropy
