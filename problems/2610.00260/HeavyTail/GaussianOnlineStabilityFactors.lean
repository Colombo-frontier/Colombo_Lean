import HeavyTail.GaussianOnlineStability
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-! Measurable, deterministically bounded factors for the actual Gaussian-mixture
online process. The bounds are independent of the observed oracle vector. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace

namespace HeavyTail.GaussianEntropy
open GaussianEstimates

variable {ι : Type*} [Fintype ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem finiteMixtureMean_ball (c : E) (R : ℝ) (centers : ι → E)
    (hc : ∀ i, ‖centers i - c‖ ≤ R) {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) :
    ‖finiteMixtureMean centers w - c‖ ≤ R := by
  have h := finiteMixtureMean_mem_convex (convex_closedBall c R)
    (centers := centers) (fun i => by simpa only [Metric.mem_closedBall, dist_eq_norm] using hc i) hw
  simpa only [Metric.mem_closedBall, dist_eq_norm] using h

theorem finiteMixtureMean_distance (c : E) (R : ℝ) (centers : ι → E)
    (hc : ∀ i, ‖centers i - c‖ ≤ R) {q w : ι → ℝ}
    (hq : q ∈ stdSimplex ℝ ι) (hw : w ∈ stdSimplex ℝ ι) :
    ‖finiteMixtureMean centers q - finiteMixtureMean centers w‖ ≤ 2 * R := by
  have hqball := finiteMixtureMean_ball E c R centers hc hq
  have hwball := finiteMixtureMean_ball E c R centers hc hw
  have he : finiteMixtureMean centers q - finiteMixtureMean centers w =
      (finiteMixtureMean centers q - c) - (finiteMixtureMean centers w - c) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

theorem center_finiteMixtureMean_distance (c : E) (R : ℝ) (centers : ι → E)
    (hc : ∀ i, ‖centers i - c‖ ≤ R) {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) (i : ι) :
    ‖centers i - finiteMixtureMean centers w‖ ≤ 2 * R := by
  have hwball := finiteMixtureMean_ball E c R centers hc hw
  have he : centers i - finiteMixtureMean centers w =
      (centers i - c) - (finiteMixtureMean centers w - c) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith [hc i])

theorem onlineMixtureW_measurable (c : E) (a η : ℝ) (centers : ι → E) :
    Measurable (fun p : SimplexPoint ι × (E × (E × E)) =>
      onlineMixtureW E c a η centers p.1.val p.2.1 p.2.2.1 p.2.2.2) := by
  let F : (SimplexPoint ι × (E × (E × E))) × E → ℝ := fun p =>
    physicalMixtureDensity E c a centers p.1.1.val p.2 *
      Real.exp (-onlineMixtureError E η p.1.2.1 p.1.2.2.1 p.1.2.2.2 (c + a • p.2))
  have hF : StronglyMeasurable F := by
    apply Continuous.stronglyMeasurable
    unfold F physicalMixtureDensity
    simp only [mixtureDensity_eq_sum]
    unfold gaussianExponentialDensity gaussianLogDensity onlineMixtureError clip
    apply Continuous.mul
    · apply continuous_finset_sum
      intro i _
      apply Continuous.mul
      · exact (continuous_apply i).comp (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))
      · fun_prop
    · fun_prop
  have h := (hF.integral_prod_right' (ν := euclideanGaussianLaw E)).measurable
  convert h using 1
  funext p
  exact integral_physicalGaussianMixtureLaw E c a centers p.1.property (by
    unfold onlineMixtureError clip
    fun_prop)

theorem onlineMixtureError_integral_measurable (c : E) {a : ℝ} (ha : a ≠ 0) (η : ℝ)
    (centers : ι → E) {q : ι → ℝ} (hq : q ∈ stdSimplex ℝ ι) :
    Measurable (fun p : E × (E × SimplexPoint ι) =>
      ∫ u, onlineMixtureError E η p.1 p.2.1 (finiteMixtureMean centers p.2.2.val) u
        ∂physicalGaussianMixtureLaw E c a centers q) := by
  simp_rw [onlineMixtureError_integral E c ha η centers hq]
  have hL : Measurable (fun p : E × (E × SimplexPoint ι) =>
      observedClippedLoss E c a η centers (p.1, p.2.2.val) q) :=
    ((observedClippedLoss_continuous E c a η centers).measurable.comp
      (measurable_fst.prodMk (measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)))).apply_continuousLinearMap q
  apply hL.sub
  exact measurable_const.mul ((measurable_fst.comp measurable_snd).inner
    (measurable_const.sub ((finiteMixtureMean centers).continuous.measurable.comp
      (measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)))))

theorem onlineMixtureError_integral_bound (c b : E) {a η M R : ℝ}
    (ha : a ≠ 0) (hη : 0 ≤ η) (hM : 0 ≤ M) (hb : ‖b‖ ≤ M)
    (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    {q w : ι → ℝ} (hq : q ∈ stdSimplex ℝ ι) (hw : w ∈ stdSimplex ℝ ι) (Y : E) :
    |∫ u, onlineMixtureError E η Y b (finiteMixtureMean centers w) u
      ∂physicalGaussianMixtureLaw E c a centers q| ≤ 1 + 2 * η * M * R := by
  rw [onlineMixtureError_integral E c ha η centers hq w Y b]
  have hclip := physical_mixture_clip_integral_bound E c a η centers hq Y (finiteMixtureMean centers w)
  rw [← observedClippedLoss_eq_expectation E c a η centers (Y, w) hq] at hclip
  have hdist := finiteMixtureMean_distance E c R centers hc hq hw
  have hin := (abs_real_inner_le_norm b _).trans (mul_le_mul hb hdist (norm_nonneg _) hM)
  have hinη := mul_le_mul_of_nonneg_left hin hη
  have habs : |η * ⟪b, finiteMixtureMean centers q - finiteMixtureMean centers w⟫_ℝ| ≤
      2 * η * M * R := by
    rw [abs_mul, abs_of_nonneg hη]
    nlinarith only [hinη]
  exact (abs_sub _ _).trans (by linarith)

theorem onlineMixture_comparator_factor_bound (c b : E) {a η M R : ℝ}
    (ha : a ≠ 0) (hη : 0 ≤ η) (hM : 0 ≤ M) (hb : ‖b‖ ≤ M)
    (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    {q w : ι → ℝ} (hq : q ∈ stdSimplex ℝ ι) (hw : w ∈ stdSimplex ℝ ι) (Y : E) :
    Real.exp (∫ u, onlineMixtureError E η Y b (finiteMixtureMean centers w) u
      ∂physicalGaussianMixtureLaw E c a centers q) ≤ Real.exp (1 + 2 * η * M * R) :=
  Real.exp_le_exp.mpr ((le_abs_self _).trans
    (onlineMixtureError_integral_bound E c b ha hη hM hb centers hc hq hw Y))

theorem onlineMixtureW_ball_bound (c b : E) {a η M R : ℝ}
    (ha : a ≠ 0) (hη : 0 ≤ η) (hM : 0 ≤ M) (hb : ‖b‖ ≤ M)
    (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) (Y : E) :
    onlineMixtureW E c a η centers w Y b (finiteMixtureMean centers w) ≤
      Real.exp (1 + 2 * η * M * R + η ^ 2 * a ^ 2 * M ^ 2 / 2) :=
  onlineMixtureW_bound E c b _ ha hη hM hb centers
    (center_finiteMixtureMean_distance E c R centers hc hw) hw Y

end HeavyTail.GaussianEntropy
