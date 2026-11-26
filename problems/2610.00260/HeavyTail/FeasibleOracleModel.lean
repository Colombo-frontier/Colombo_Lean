import HeavyTail.OracleModel
import HeavyTail.FeasibleReduction
import HeavyTail.WarmStart
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.MapComap

/-! The manuscript's actual public query rule and corrected raw observations,
instantiated in the full information model. The anchor, proximal search and
observation transformation use public data only. All mean and moment claims
are derived from PrivateInstance's original raw-oracle contract. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace
namespace HeavyTail
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {θ : OracleParameters}

namespace PublicProblem

def relativeInteriorAnchor (B : PublicProblem E θ) : E :=
  (B.X_nonempty.intrinsicInterior B.X_convex).choose

theorem relativeInteriorAnchor_mem (B : PublicProblem E θ) :
    B.relativeInteriorAnchor ∈ intrinsicInterior ℝ B.X :=
  (B.X_nonempty.intrinsicInterior B.X_convex).choose_spec

def stageQuery (B : PublicProblem E θ) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (z : E) : B.X :=
  ⟨feasibleOracleQuery B.prox θ.G_pos hR hn B.relativeInteriorAnchor z,
    intrinsicInterior_subset (feasibleOracleQuery_relativeInterior B.prox B.X_convex
      B.domain_subset θ.G_pos hR hn B.relativeInteriorAnchor z B.relativeInteriorAnchor_mem)⟩

theorem stageQuery_measurable (B : PublicProblem E θ) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) : Measurable (B.stageQuery hR hn) :=
  (feasibleOracleQuery_measurable B.prox B.h_convex θ.G_pos hR hn B.relativeInteriorAnchor).subtype_mk

def stageCorrection (B : PublicProblem E θ) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (z : E) : E :=
  selectedProximalCorrection B.prox θ.G_pos hR hn z

def correctedReply (B : PublicProblem E θ) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (z g : E) : E :=
  ambientProjection (affineSpan ℝ B.X).direction g + B.stageCorrection hR hn z

theorem stageCorrection_measurable (B : PublicProblem E θ) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) : Measurable (B.stageCorrection hR hn) :=
  selectedProximalCorrection_measurable B.prox B.h_convex θ.G_pos hR hn

theorem correctedReply_measurable (B : PublicProblem E θ) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) : Measurable (fun zg : E × E => B.correctedReply hR hn zg.1 zg.2) :=
  ((ambientProjection (affineSpan ℝ B.X).direction).continuous.measurable.comp measurable_snd).add
    ((B.stageCorrection_measurable hR hn).comp measurable_fst)

theorem correctedReply_measurable_right (B : PublicProblem E θ) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (z : E) : Measurable (B.correctedReply hR hn z) :=
  (B.correctedReply_measurable hR hn).comp measurable_prodMk_left

end PublicProblem

namespace PrivateInstance
variable {B : PublicProblem E θ}

theorem lipschitz_difference (I : PrivateInstance B) (u : E) (hu : u ∈ B.X)
    (v : E) (hv : v ∈ B.X) : I.f u - I.f v ≤ θ.G * ‖u - v‖ := by
  have h := I.f_lipschitz.dist_le_mul u hu v hv
  rw [Real.dist_eq, dist_eq_norm] at h
  exact (le_abs_self _).trans h

theorem rawNoise_centered (I : PrivateInstance B) (x : B.X) :
    (∫ g, g - I.mean x ∂I.oracle x) = 0 := by
  rw [integral_sub (I.reply_integrable x) (integrable_const _), integral_const]
  simp [mean]

def stageRawKernel (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) : Kernel E E :=
  I.oracle.comap (B.stageQuery hR hn) (B.stageQuery_measurable hR hn)

instance stageRawKernel_markov (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) : IsMarkovKernel (I.stageRawKernel hR hn) := by
  unfold stageRawKernel
  infer_instance

def correctedKernel (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) : Kernel E E where
  toFun z := (I.oracle (B.stageQuery hR hn z)).map (B.correctedReply hR hn z)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have hm := Kernel.measurable_kernel_prodMk_left (κ := I.stageRawKernel hR hn)
      (hA.preimage (B.correctedReply_measurable hR hn))
    simpa only [Measure.map_apply (B.correctedReply_measurable_right hR hn _) hA] using hm

instance correctedKernel_markov (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) : IsMarkovKernel (I.correctedKernel hR hn) := by
  constructor
  intro z
  exact isProbabilityMeasure_map (B.correctedReply_measurable_right hR hn z).aemeasurable

def correctedMean (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (z : E) : E :=
  ambientProjection (affineSpan ℝ B.X).direction (I.mean (B.stageQuery hR hn z)) +
    B.stageCorrection hR hn z

theorem correctedReply_integrable (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (z : E) :
    Integrable (B.correctedReply hR hn z) (I.stageRawKernel hR hn z) :=
  ((ambientProjection (affineSpan ℝ B.X).direction).integrable_comp
    (I.reply_integrable (B.stageQuery hR hn z))).add (integrable_const _)

theorem correctedMean_eq_integral (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (z : E) :
    (∫ g, B.correctedReply hR hn z g ∂I.stageRawKernel hR hn z) = I.correctedMean hR hn z :=
  correctedProjected_observation_mean _ (I.reply_integrable (B.stageQuery hR hn z)) _

theorem correctedKernel_mean (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (z : E) :
    (∫ g, g ∂I.correctedKernel hR hn z) = I.correctedMean hR hn z := by
  change (∫ g, id g ∂(I.oracle (B.stageQuery hR hn z)).map (B.correctedReply hR hn z)) = _
  rw [integral_map (B.correctedReply_measurable_right hR hn z).aemeasurable
    measurable_id.aestronglyMeasurable]
  exact I.correctedMean_eq_integral hR hn z

theorem correctedReply_center (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (z g : E) :
    B.correctedReply hR hn z g - I.correctedMean hR hn z =
      ambientProjection (affineSpan ℝ B.X).direction (g - I.mean (B.stageQuery hR hn z)) :=
  correctedProjected_observation_center _ id _ _ g

theorem correctedReply_noise_memLp (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (z : E) :
    MemLp (fun g => B.correctedReply hR hn z g - I.correctedMean hR hn z)
      (ENNReal.ofReal θ.p) (I.stageRawKernel hR hn z) := by
  simp_rw [I.correctedReply_center]
  exact projectedNoise_memLp _ (I.noise_memLp (B.stageQuery hR hn z))

theorem correctedReply_strong_moment (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (z : E) :
    (∫ g, ‖B.correctedReply hR hn z g - I.correctedMean hR hn z‖ ^ θ.p
      ∂I.stageRawKernel hR hn z) ≤ θ.L ^ θ.p := by
  simp_rw [I.correctedReply_center]
  exact projectedNoise_norm_moment _ (lt_trans zero_lt_one θ.p_gt_one)
    (I.noise_memLp (B.stageQuery hR hn z)) (I.strong_moment (B.stageQuery hR hn z))

theorem correctedReply_weak_moment (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (z v : E) (hv : ‖v‖ = 1) :
    (∫ g, |⟪v, B.correctedReply hR hn z g - I.correctedMean hR hn z⟫_ℝ| ^ θ.p
      ∂I.stageRawKernel hR hn z) ≤ θ.s ^ θ.p := by
  simp_rw [I.correctedReply_center]
  exact projectedNoise_weak_moment _ (lt_trans zero_lt_one θ.p_gt_one) θ.s_pos.le
    (I.weak_moment (B.stageQuery hR hn z)) v hv

theorem correctedMean_bound_transfer (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (z : E) (hz : ‖z - I.minimizer‖ ≤ 2 * R) :
    ‖I.correctedMean hR hn z‖ ≤ 4 * θ.G ∧
    I.f (selectedProximalPoint B.prox θ.G_pos hR hn z) +
      B.h (selectedProximalPoint B.prox θ.G_pos hR hn z) - I.optimalValue ≤
      ⟪I.correctedMean hR hn z, z - I.minimizer⟫_ℝ + θ.G * R / (2 * n) := by
  apply feasible_corrected_mean_transfer B.prox B.h_convex B.X_convex B.domain_subset
    θ.G_pos hR hn B.relativeInteriorAnchor z I.minimizer (I.mean (B.stageQuery hR hn z))
    B.relativeInteriorAnchor_mem I.minimizer_domain hz I.minimizing I.lipschitz_difference
  intro u hu
  have h := I.mean_subgradient (B.stageQuery hR hn z) u hu
  change I.f (feasibleOracleQuery B.prox θ.G_pos hR hn B.relativeInteriorAnchor z) +
    ⟪I.mean (B.stageQuery hR hn z),
      u - feasibleOracleQuery B.prox θ.G_pos hR hn B.relativeInteriorAnchor z⟫_ℝ ≤ I.f u at h
  linarith only [h]

theorem model_warm_start (I : PrivateInstance B) (hμ : 0 < θ.μ) :
    warmStartPoint B.prox θ.μ θ.D θ.G B.initial ∈ B.X ∧
    ‖warmStartPoint B.prox θ.μ θ.D θ.G B.initial - I.minimizer‖ ≤
      warmStartRadius θ.μ θ.D θ.G ∧
    warmStartRadius θ.μ θ.D θ.G ≤ Real.sqrt 2 * θ.G / θ.μ := by
  refine ⟨warmStartPoint_feasible B.prox B.domain_subset θ.μ_nonneg θ.D_pos θ.G_pos
    B.initial B.initial_feasible, ?_⟩
  exact finite_proximal_warm_start_radius B.prox
    (I.f_convex.subset B.domain_subset B.h_convex.1) B.h_strongConvex hμ θ.D_pos θ.G_pos
    B.initial I.minimizer I.minimizer_domain I.initial_distance I.minimizing
    (fun u hu => I.lipschitz_difference u (B.domain_subset hu) I.minimizer
      (B.domain_subset I.minimizer_domain))

end PrivateInstance
end HeavyTail
