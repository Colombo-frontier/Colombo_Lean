import HeavyTail.GaussianOnlineStabilityFactors
import HeavyTail.GaussianOnlineStabilityLaw
import HeavyTail.GaussianMixedBound

/-! One-step exponential moments of the actual learner factors, obtained
from centered oracle moments and the proved Gaussian mixed-exponential bound. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace

namespace HeavyTail.GaussianEntropy
open GaussianEstimates

variable {ι : Type*} [Fintype ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem signed_online_error_exp_bound (η ε : ℝ) (hε : ε = -1 ∨ ε = 1) (Y b x u : E) :
    Real.exp (ε * onlineMixtureError E η Y b x u) ≤
      Real.exp 1 * Real.exp ((-ε * η) * ⟪b, u - x⟫_ℝ) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  unfold onlineMixtureError
  rcases hε with rfl | rfl <;> nlinarith [clip_mem (η * ⟪Y, u - x⟫_ℝ)]

theorem signed_online_error_exp_integrable (c : E) (a η ε : ℝ)
    (hε : ε = -1 ∨ ε = 1) (centers : ι → E) {w : ι → ℝ}
    (hw : w ∈ stdSimplex ℝ ι) (Y b x : E) :
    Integrable (fun u => Real.exp (ε * onlineMixtureError E η Y b x u))
      (physicalGaussianMixtureLaw E c a centers w) := by
  apply ((physical_mixture_exp_integrable E c b x a (-ε * η) centers hw).const_mul (Real.exp 1)).mono'
  · apply Measurable.aestronglyMeasurable
    unfold onlineMixtureError clip
    fun_prop
  · apply ae_of_all
    intro u
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact signed_online_error_exp_bound E η ε hε Y b x u

theorem signed_online_error_component_integrable (center : E) (a η ε : ℝ)
    (hε : ε = -1 ∨ ε = 1) (Y b x : E) :
    Integrable (fun z => Real.exp (ε * onlineMixtureError E η Y b x (center + a • z)))
      (euclideanGaussianLaw E) := by
  have hi : Integrable (fun z : E => Real.exp ((-ε * η) * ⟪b, center + a • z - x⟫_ℝ))
      (euclideanGaussianLaw E) := by
    simp_rw [physical_exp_eq_affine]
    exact gaussian_affine_exp_integrable E _ _
  apply (hi.const_mul (Real.exp 1)).mono'
  · apply Measurable.aestronglyMeasurable
    unfold onlineMixtureError clip
    fun_prop
  · apply ae_of_all
    intro z
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact signed_online_error_exp_bound E η ε hε Y b x (center + a • z)

def signedOnlineFactor (c : E) (a η ε : ℝ) (centers : ι → E)
    (w : ι → ℝ) (Y b x : E) : ℝ :=
  ∫ u, Real.exp (ε * onlineMixtureError E η Y b x u) ∂physicalGaussianMixtureLaw E c a centers w

theorem signedOnlineFactor_eq_sum (c : E) {a : ℝ} (ha : a ≠ 0) (η ε : ℝ)
    (hε : ε = -1 ∨ ε = 1) (centers : ι → E) {w : ι → ℝ}
    (hw : w ∈ stdSimplex ℝ ι) (Y b x : E) :
    signedOnlineFactor E c a η ε centers w Y b x =
      ∑ i, w i * ∫ z, Real.exp (ε * onlineMixtureError E η Y b x (centers i + a • z))
        ∂euclideanGaussianLaw E :=
  integral_physicalGaussianMixtureLaw_sum E c ha centers hw (by
    unfold onlineMixtureError clip
    fun_prop) (fun i => signed_online_error_component_integrable E (centers i) a η ε hε Y b x)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem signed_online_factor_moment {ξ : Ω → E} (hξ : Measurable ξ)
    (h2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) P) (hcenter : (∫ ω, ξ ω ∂P) = 0)
    {p s V M R η a : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 < s)
    (hV : (∫ ω, ‖ξ ω‖ ^ 2 ∂P) ≤ V)
    (hweak : ∀ v : E, ‖v‖ = 1 → (∫ ω, |⟪v, ξ ω⟫_ℝ| ^ p ∂P) ≤ s ^ p)
    (c b x : E) (hb : ‖b‖ ≤ M)
    (hη : 0 ≤ η) (ha : 0 < a) (haR : a ≤ R) (htune : η * M * R ≤ 1 / 16)
    (centers : ι → E) (hc : ∀ i, ‖centers i - x‖ ≤ 2 * R)
    {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι)
    (ε : ℝ) (hε : ε = -1 ∨ ε = 1) :
    Integrable (fun ω => signedOnlineFactor E c a η ε centers w (b + ξ ω) b x) P ∧
    (∫ ω, signedOnlineFactor E c a η ε centers w (b + ξ ω) b x ∂P) ≤
      Real.exp (mixedConstant p * (η ^ p * (s * R) ^ p + η ^ 2 * a ^ 2 * (V + M ^ 2))) := by
  let F (i : ι) : Ω × E → ℝ := fixedMixedExp E ξ b (centers i - x) η a ε
  have hfi (i : ι) : Integrable (F i) (P.prod (euclideanGaussianLaw E)) :=
    fixedMixedExp_integrable E hξ b (centers i - x) η a ε hε
  have heq : (fun ω => signedOnlineFactor E c a η ε centers w (b + ξ ω) b x) =
      (fun ω => ∑ i, w i * ∫ z, F i (ω, z) ∂euclideanGaussianLaw E) := by
    funext ω
    rw [signedOnlineFactor_eq_sum E c ha.ne' η ε hε centers hw]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply integral_congr_ae
    apply ae_of_all
    intro z
    unfold F fixedMixedExp onlineMixtureError
    dsimp only
    rw [show centers i + a • z - x = (centers i - x) + a • z by abel]
  have hi (i : ι) : Integrable (fun ω => w i * ∫ z, F i (ω, z) ∂euclideanGaussianLaw E) P :=
    (hfi i).integral_prod_left.const_mul (w i)
  rw [heq]
  refine ⟨integrable_finset_sum _ (fun i _ => hi i), ?_⟩
  rw [integral_finset_sum _ (fun i _ => hi i)]
  simp only [integral_const_mul]
  have hterm (i : ι) : (∫ ω, ∫ z, F i (ω, z) ∂euclideanGaussianLaw E ∂P) ≤
      Real.exp (mixedConstant p * (η ^ p * (s * R) ^ p + η ^ 2 * a ^ 2 * (V + M ^ 2))) := by
    rw [← integral_prod _ (hfi i)]
    exact fixed_mixed_exp_bound E hξ h2 hcenter hp hp2 hs hV hweak b (centers i - x)
      hb (hc i) hη ha haR htune ε hε
  calc
    _ ≤ ∑ i, w i * Real.exp (mixedConstant p *
        (η ^ p * (s * R) ^ p + η ^ 2 * a ^ 2 * (V + M ^ 2))) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hterm i) (hw.1 i))
    _ = _ := by rw [← Finset.sum_mul, hw.2, one_mul]

end HeavyTail.GaussianEntropy
