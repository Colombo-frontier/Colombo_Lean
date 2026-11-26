import HeavyTail.MixtureDifferentiation
import HeavyTail.EntropyVariational
import HeavyTail.MirrorDescent
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Entropy of finite mixtures of actual positive densities

The entropy, its derivative and the component densities are concrete integrals.
The analytic assumptions are explicit integrability and an integrable
first-difference envelope on the simplex. No derivative, Bregman identity, or
minimizer conclusion is assumed. Gaussian-specific envelope verification and
measurability of a minimizer selection are separate obligations.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace HeavyTail

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {μ : Measure Ω}

def mixtureLinear (φ : ι → Ω → ℝ) (ω : Ω) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, (φ i ω) • ContinuousLinearMap.proj i

def mixtureDensity (φ : ι → Ω → ℝ) (w : ι → ℝ) (ω : Ω) : ℝ :=
  mixtureLinear φ ω w

omit [MeasurableSpace Ω] in
theorem mixtureDensity_eq_sum (φ : ι → Ω → ℝ) (w : ι → ℝ) (ω : Ω) :
    mixtureDensity φ w ω = ∑ i, w i * φ i ω := by
  simp [mixtureDensity, mixtureLinear, mul_comm]

omit [MeasurableSpace Ω] in
theorem mixtureDensity_pos {φ : ι → Ω → ℝ} {w : ι → ℝ}
    (hφ : ∀ i ω, 0 < φ i ω) (hw : w ∈ stdSimplex ℝ ι) (ω : Ω) :
    0 < mixtureDensity φ w ω := by
  have hex : ∃ i, 0 < w i := by
    by_contra h
    push_neg at h
    have hs : ∑ i, w i ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
    linarith [hw.2]
  obtain ⟨i, hi⟩ := hex
  rw [mixtureDensity_eq_sum]
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hw.1 j) (hφ j ω).le)
    ⟨i, Finset.mem_univ _, mul_pos hi (hφ i ω)⟩

theorem mixtureDensity_measurable {φ : ι → Ω → ℝ}
    (hφ : ∀ i, Measurable (φ i)) (w : ι → ℝ) : Measurable (mixtureDensity φ w) := by
  have heq : mixtureDensity φ w = (fun ω => ∑ i, w i * φ i ω) := funext (mixtureDensity_eq_sum φ w)
  rw [heq]
  exact Finset.measurable_sum _ (fun i _ => (hφ i).const_mul (w i))

theorem mixtureDensity_integrable {φ : ι → Ω → ℝ}
    (hφ : ∀ i, Integrable (φ i) μ) (w : ι → ℝ) : Integrable (mixtureDensity φ w) μ := by
  have heq : mixtureDensity φ w = (fun ω => ∑ i, w i * φ i ω) := funext (mixtureDensity_eq_sum φ w)
  rw [heq]
  exact integrable_finset_sum _ (fun i _ => (hφ i).const_mul (w i))

theorem mixtureDensity_normalized {φ : ι → Ω → ℝ} {w : ι → ℝ}
    (hφ : ∀ i, Integrable (φ i) μ) (hmass : ∀ i, (∫ ω, φ i ω ∂μ) = 1)
    (hw : w ∈ stdSimplex ℝ ι) : (∫ ω, mixtureDensity φ w ω ∂μ) = 1 := by
  simp_rw [mixtureDensity_eq_sum]
  rw [integral_finset_sum _ (fun i _ => (hφ i).const_mul (w i))]
  simp_rw [integral_const_mul, hmass, mul_one]
  exact hw.2

theorem mixtureDensity_probability {φ : ι → Ω → ℝ} {w : ι → ℝ}
    (hφpos : ∀ i ω, 0 < φ i ω) (hφint : ∀ i, Integrable (φ i) μ)
    (hmass : ∀ i, (∫ ω, φ i ω ∂μ) = 1) (hw : w ∈ stdSimplex ℝ ι) :
    IsProbabilityMeasure (densityMeasure μ (mixtureDensity φ w)) :=
  densityMeasure_isProbability (fun ω => (mixtureDensity_pos hφpos hw ω).le)
    (mixtureDensity_integrable hφint w) (mixtureDensity_normalized hφint hmass hw)

def mixtureEntropyIntegrand (φ : ι → Ω → ℝ) (w : ι → ℝ) (ω : Ω) : ℝ :=
  mixtureDensity φ w ω * Real.log (mixtureDensity φ w ω)

def mixtureEntropy (μ : Measure Ω) (φ : ι → Ω → ℝ) (w : ι → ℝ) : ℝ :=
  ∫ ω, mixtureEntropyIntegrand φ w ω ∂μ

def mixtureEntropyDifferential (φ : ι → Ω → ℝ) (w : ι → ℝ)
    (ω : Ω) : (ι → ℝ) →L[ℝ] ℝ :=
  (Real.log (mixtureDensity φ w ω) + 1) • mixtureLinear φ ω

def mixtureEntropyDerivative (μ : Measure Ω) (φ : ι → Ω → ℝ)
    (w : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∫ ω, mixtureEntropyDifferential φ w ω ∂μ

omit [MeasurableSpace Ω] in
theorem mixtureEntropy_pointwise_derivative {φ : ι → Ω → ℝ} {w : ι → ℝ}
    (hφpos : ∀ i ω, 0 < φ i ω) (hw : w ∈ stdSimplex ℝ ι) (ω : Ω) :
    HasFDerivAt (fun v => mixtureEntropyIntegrand φ v ω)
      (mixtureEntropyDifferential φ w ω) w := by
  exact (Real.hasDerivAt_mul_log (mixtureDensity_pos hφpos hw ω).ne').comp_hasFDerivAt
    w (mixtureLinear φ ω).hasFDerivAt

/-- Integral convexity is proved pointwise, then integrated. -/
theorem mixtureEntropy_convex {φ : ι → Ω → ℝ}
    (hφpos : ∀ i ω, 0 < φ i ω)
    (hent : ∀ w ∈ stdSimplex ℝ ι, Integrable (mixtureEntropyIntegrand φ w) μ) :
    ConvexOn ℝ (stdSimplex ℝ ι) (mixtureEntropy μ φ) := by
  refine ⟨convex_stdSimplex ℝ ι, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy := (convex_stdSimplex ℝ ι) hx hy ha hb hab
  have hi := integral_mono (hent _ hxy) ((hent x hx).const_mul a |>.add ((hent y hy).const_mul b))
    (fun ω => by
      have h := Real.convexOn_mul_log.2
        (show mixtureDensity φ x ω ∈ Ici (0 : ℝ) from (mixtureDensity_pos hφpos hx ω).le)
        (show mixtureDensity φ y ω ∈ Ici (0 : ℝ) from (mixtureDensity_pos hφpos hy ω).le)
        ha hb hab
      simpa only [mixtureEntropyIntegrand, mixtureDensity, map_add, map_smul,
        smul_eq_mul] using h)
  change (∫ ω, mixtureEntropyIntegrand φ (a • x + b • y) ω ∂μ) ≤
    ∫ ω, a * mixtureEntropyIntegrand φ x ω + b * mixtureEntropyIntegrand φ y ω ∂μ at hi
  rw [integral_add ((hent x hx).const_mul a) ((hent y hy).const_mul b),
    integral_const_mul, integral_const_mul] at hi
  exact hi

/-- A genuine within-simplex derivative, obtained by dominated differentiation. -/
theorem mixtureEntropy_hasFDerivWithinAt {φ : ι → Ω → ℝ} {w : ι → ℝ} {B : Ω → ℝ}
    (hφpos : ∀ i ω, 0 < φ i ω) (hw : w ∈ stdSimplex ℝ ι)
    (hent : ∀ v ∈ stdSimplex ℝ ι, Integrable (mixtureEntropyIntegrand φ v) μ)
    (hdint : Integrable (mixtureEntropyDifferential φ w) μ)
    (hB : Integrable B μ) (hBpos : ∀ ω, 0 ≤ B ω)
    (hdom : ∀ᵐ ω ∂μ, ∀ v ∈ stdSimplex ℝ ι,
      ‖mixtureEntropyIntegrand φ v ω - mixtureEntropyIntegrand φ w ω‖ ≤ B ω * ‖v - w‖) :
    HasFDerivWithinAt (mixtureEntropy μ φ) (mixtureEntropyDerivative μ φ w)
      (stdSimplex ℝ ι) w := by
  apply hasFDerivWithinAt_integral_of_dominated_difference hw hent hdint hB hBpos hdom
  exact Filter.Eventually.of_forall (fun ω =>
    (mixtureEntropy_pointwise_derivative hφpos hw ω).hasFDerivWithinAt)

theorem mixtureEntropy_continuousOn {φ : ι → Ω → ℝ}
    (hφpos : ∀ i ω, 0 < φ i ω)
    (hent : ∀ w ∈ stdSimplex ℝ ι, Integrable (mixtureEntropyIntegrand φ w) μ)
    (hdint : ∀ w ∈ stdSimplex ℝ ι, Integrable (mixtureEntropyDifferential φ w) μ)
    (hdom : ∀ w ∈ stdSimplex ℝ ι, ∃ B : Ω → ℝ,
      Integrable B μ ∧ (∀ ω, 0 ≤ B ω) ∧
      (∀ᵐ ω ∂μ, ∀ v ∈ stdSimplex ℝ ι,
        ‖mixtureEntropyIntegrand φ v ω - mixtureEntropyIntegrand φ w ω‖ ≤ B ω * ‖v - w‖)) :
    ContinuousOn (mixtureEntropy μ φ) (stdSimplex ℝ ι) := by
  intro w hw
  obtain ⟨B, hB, hBpos, hbound⟩ := hdom w hw
  exact (mixtureEntropy_hasFDerivWithinAt hφpos hw hent (hdint w hw) hB hBpos hbound).continuousWithinAt

/-- The derivative evaluates as the actual integral of `(1+log q) δq`. -/
theorem mixtureEntropyDerivative_apply {φ : ι → Ω → ℝ} {w : ι → ℝ}
    (hdint : Integrable (mixtureEntropyDifferential φ w) μ) (v : ι → ℝ) :
    mixtureEntropyDerivative μ φ w v =
      ∫ ω, (Real.log (mixtureDensity φ w ω) + 1) * mixtureDensity φ v ω ∂μ := by
  rw [mixtureEntropyDerivative, ContinuousLinearMap.integral_apply hdint]
  rfl

/-- The Bregman divergence of the actual mixture entropy equals the density KL. -/
theorem mixtureEntropy_bregman_eq_KL {φ : ι → Ω → ℝ} {q p : ι → ℝ}
    (hφpos : ∀ i ω, 0 < φ i ω) (hφint : ∀ i, Integrable (φ i) μ)
    (hmass : ∀ i, (∫ ω, φ i ω ∂μ) = 1)
    (hq : q ∈ stdSimplex ℝ ι) (hp : p ∈ stdSimplex ℝ ι)
    (hqent : Integrable (mixtureEntropyIntegrand φ q) μ)
    (hpent : Integrable (mixtureEntropyIntegrand φ p) μ)
    (hdint : Integrable (mixtureEntropyDifferential φ p) μ) :
    bregmanDivergence (mixtureEntropy μ φ) (mixtureEntropyDerivative μ φ) q p =
      densityRelativeEntropy μ (mixtureDensity φ q) (mixtureDensity φ p) := by
  have hD : Integrable (fun ω => mixtureEntropyDifferential φ p ω (q - p)) μ :=
    hdint.apply_continuousLinearMap _
  have hdelta : Integrable (fun ω => mixtureDensity φ q ω - mixtureDensity φ p ω) μ :=
    (mixtureDensity_integrable hφint q).sub (mixtureDensity_integrable hφint p)
  have hbase : Integrable (fun ω => mixtureEntropyIntegrand φ q ω -
      mixtureEntropyIntegrand φ p ω - mixtureEntropyDifferential φ p ω (q - p)) μ :=
    (hqent.sub hpent).sub hD
  have heq : (fun ω => mixtureDensity φ q ω * Real.log (mixtureDensity φ q ω / mixtureDensity φ p ω)) =
      (fun ω => (mixtureEntropyIntegrand φ q ω - mixtureEntropyIntegrand φ p ω -
        mixtureEntropyDifferential φ p ω (q - p)) +
          (mixtureDensity φ q ω - mixtureDensity φ p ω)) := by
    funext ω
    rw [Real.log_div (mixtureDensity_pos hφpos hq ω).ne' (mixtureDensity_pos hφpos hp ω).ne']
    simp only [mixtureEntropyIntegrand, mixtureEntropyDifferential,
      ContinuousLinearMap.smul_apply, smul_eq_mul, map_sub, mixtureDensity]
    ring
  have hsubent : Integrable (fun ω => mixtureEntropyIntegrand φ q ω - mixtureEntropyIntegrand φ p ω) μ :=
    hqent.sub hpent
  have hi : (∫ ω, mixtureDensity φ q ω * Real.log (mixtureDensity φ q ω / mixtureDensity φ p ω) ∂μ) =
      (∫ ω, mixtureEntropyIntegrand φ q ω ∂μ) - (∫ ω, mixtureEntropyIntegrand φ p ω ∂μ) -
        (∫ ω, mixtureEntropyDifferential φ p ω (q - p) ∂μ) := by
    rw [heq, integral_add hbase hdelta, integral_sub hsubent hD,
      integral_sub hqent hpent, integral_sub (mixtureDensity_integrable hφint q)
        (mixtureDensity_integrable hφint p),
      mixtureDensity_normalized hφint hmass hq, mixtureDensity_normalized hφint hmass hp]
    ring
  unfold bregmanDivergence mixtureEntropy mixtureEntropyDerivative densityRelativeEntropy
  rw [ContinuousLinearMap.integral_apply hdint]
  exact hi.symm

/-- A mirror optimizer exists on the actual compact simplex. Selection measurability is separate. -/
theorem exists_mixtureEntropy_mirror_minimizer [Nonempty ι] {φ : ι → Ω → ℝ}
    (hφpos : ∀ i ω, 0 < φ i ω)
    (hent : ∀ w ∈ stdSimplex ℝ ι, Integrable (mixtureEntropyIntegrand φ w) μ)
    (hdint : ∀ w ∈ stdSimplex ℝ ι, Integrable (mixtureEntropyDifferential φ w) μ)
    (hdom : ∀ w ∈ stdSimplex ℝ ι, ∃ B : Ω → ℝ,
      Integrable B μ ∧ (∀ ω, 0 ≤ B ω) ∧
      (∀ᵐ ω ∂μ, ∀ v ∈ stdSimplex ℝ ι,
        ‖mixtureEntropyIntegrand φ v ω - mixtureEntropyIntegrand φ w ω‖ ≤ B ω * ‖v - w‖))
    (L : (ι → ℝ) →L[ℝ] ℝ) (x : ι → ℝ) :
    ∃ y ∈ stdSimplex ℝ ι, IsMinOn
      (fun z => L z + bregmanDivergence (mixtureEntropy μ φ) (mixtureEntropyDerivative μ φ) z x)
        (stdSimplex ℝ ι) y := by
  classical
  apply (isCompact_stdSimplex ι).exists_isMinOn
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨Pi.single i 1, single_mem_stdSimplex ℝ i⟩
  · intro w hw
    obtain ⟨B, hB, hBpos, hbound⟩ := hdom w hw
    exact (mirror_objective_derivative L
      (mixtureEntropy_hasFDerivWithinAt hφpos hw hent (hdint w hw) hB hBpos hbound)).continuousWithinAt

section MeanPenalty

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def meanRegularizedEntropy (μ : Measure Ω) (φ : ι → Ω → ℝ) (β : ℝ)
    (M : (ι → ℝ) →L[ℝ] V) (w : ι → ℝ) : ℝ :=
  mixtureEntropy μ φ w + β / 2 * ‖M w‖ ^ 2

def meanRegularizedEntropyDerivative (μ : Measure Ω) (φ : ι → Ω → ℝ) (β : ℝ)
    (M : (ι → ℝ) →L[ℝ] V) (w : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  mixtureEntropyDerivative μ φ w + β • (innerSL ℝ (M w)).comp M

omit [MeasurableSpace Ω] in
theorem meanPenalty_derivative (β : ℝ) (M : (ι → ℝ) →L[ℝ] V) (w : ι → ℝ) :
    HasFDerivAt (fun v => β / 2 * ‖M v‖ ^ 2) (β • (innerSL ℝ (M w)).comp M) w := by
  convert (M.hasFDerivAt.norm_sq.const_mul (β / 2)) using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem meanRegularizedEntropy_hasFDerivWithinAt {φ : ι → Ω → ℝ} {w : ι → ℝ} {B : Ω → ℝ}
    (hφpos : ∀ i ω, 0 < φ i ω) (hw : w ∈ stdSimplex ℝ ι)
    (hent : ∀ v ∈ stdSimplex ℝ ι, Integrable (mixtureEntropyIntegrand φ v) μ)
    (hdint : Integrable (mixtureEntropyDifferential φ w) μ)
    (hB : Integrable B μ) (hBpos : ∀ ω, 0 ≤ B ω)
    (hdom : ∀ᵐ ω ∂μ, ∀ v ∈ stdSimplex ℝ ι,
      ‖mixtureEntropyIntegrand φ v ω - mixtureEntropyIntegrand φ w ω‖ ≤ B ω * ‖v - w‖)
    (β : ℝ) (M : (ι → ℝ) →L[ℝ] V) :
    HasFDerivWithinAt (meanRegularizedEntropy μ φ β M)
      (meanRegularizedEntropyDerivative μ φ β M w) (stdSimplex ℝ ι) w :=
  (mixtureEntropy_hasFDerivWithinAt hφpos hw hent hdint hB hBpos hdom).add
    (meanPenalty_derivative β M w).hasFDerivWithinAt

theorem meanRegularizedEntropy_bregman_identity (φ : ι → Ω → ℝ) (β : ℝ)
    (M : (ι → ℝ) →L[ℝ] V) (q p : ι → ℝ) :
    bregmanDivergence (meanRegularizedEntropy μ φ β M)
      (meanRegularizedEntropyDerivative μ φ β M) q p =
      bregmanDivergence (mixtureEntropy μ φ) (mixtureEntropyDerivative μ φ) q p +
        β / 2 * ‖M q - M p‖ ^ 2 := by
  simp only [bregmanDivergence, meanRegularizedEntropy, meanRegularizedEntropyDerivative,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply, smul_eq_mul, map_sub,
    inner_sub_right, real_inner_self_eq_norm_sq, norm_sub_sq_real]
  rw [real_inner_comm (M p) (M q)]
  ring

theorem meanRegularizedEntropy_bregman_eq_KL {φ : ι → Ω → ℝ} {q p : ι → ℝ}
    (hφpos : ∀ i ω, 0 < φ i ω) (hφint : ∀ i, Integrable (φ i) μ)
    (hmass : ∀ i, (∫ ω, φ i ω ∂μ) = 1)
    (hq : q ∈ stdSimplex ℝ ι) (hp : p ∈ stdSimplex ℝ ι)
    (hqent : Integrable (mixtureEntropyIntegrand φ q) μ)
    (hpent : Integrable (mixtureEntropyIntegrand φ p) μ)
    (hdint : Integrable (mixtureEntropyDifferential φ p) μ)
    (β : ℝ) (M : (ι → ℝ) →L[ℝ] V) :
    bregmanDivergence (meanRegularizedEntropy μ φ β M)
      (meanRegularizedEntropyDerivative μ φ β M) q p =
      densityRelativeEntropy μ (mixtureDensity φ q) (mixtureDensity φ p) +
        β / 2 * ‖M q - M p‖ ^ 2 := by
  rw [meanRegularizedEntropy_bregman_identity,
    mixtureEntropy_bregman_eq_KL hφpos hφint hmass hq hp hqent hpent hdint]

end MeanPenalty

end HeavyTail

