import HeavyTail.OracleQuadratic
import HeavyTail.ConfidenceMinimax
import HeavyTail.GaussianAdaptiveSampler

/-! The confidence hard family is an actual private instance of the full oracle
model. Its query-dependent Markov kernel is the pushforward of the two-point
erasure law; integrability, centering and both moment bounds are derived. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
namespace HeavyTail

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def confidenceKernel (e : E) (a ρ u : ℝ) (hu : u ≤ 1) (h : Bool) : Kernel E E :=
  kernelOfSampler (erasureCoin u hu).toMeasure
    (fun z : E × Bool => confidenceOracle e a ρ u h z.1 z.2)
    (confidenceOracle_measurable e a ρ u h)

instance confidenceKernel_markov (e : E) (a ρ u : ℝ) (hu : u ≤ 1) (h : Bool) :
    IsMarkovKernel (confidenceKernel e a ρ u hu h) := by
  unfold confidenceKernel
  infer_instance

theorem confidenceKernel_integrable (e : E) (a ρ u : ℝ) (hu : u ≤ 1) (h : Bool) (x : E) :
    Integrable (fun g : E => g) (confidenceKernel e a ρ u hu h x) := by
  change Integrable (fun g : E => g) ((erasureCoin u hu).toMeasure.map _)
  apply (integrable_map_measure measurable_id.aestronglyMeasurable
    (Measurable.of_discrete : Measurable (confidenceOracle e a ρ u h x)).aemeasurable).mpr
  exact memLp_one_iff_integrable.mp MemLp.of_discrete

theorem confidenceKernel_mean (e : E) (a ρ : ℝ) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (h : Bool) (x : E) :
    (∫ g, g ∂confidenceKernel e a ρ u hu1.le h x) = confidenceMean e a ρ h x := by
  change (∫ g : E, g ∂((erasureCoin u hu1.le).toMeasure.map _)) = _
  calc
    _ = ∫ b, confidenceOracle e a ρ u h x b ∂(erasureCoin u hu1.le).toMeasure :=
      integral_map (Measurable.of_discrete :
        Measurable (confidenceOracle e a ρ u h x)).aemeasurable
        (measurable_id : Measurable (fun g : E => g)).aestronglyMeasurable
    _ = _ := confidenceOracle_unbiased e a ρ hu0 hu1 h x

theorem confidenceKernel_noise_memLp (e : E) (a ρ u : ℝ) (hu : u ≤ 1)
    (h : Bool) (x : E) (p : ℝ≥0∞) :
    MemLp (fun g => g - ∫ z, z ∂confidenceKernel e a ρ u hu h x) p
      (confidenceKernel e a ρ u hu h x) := by
  change MemLp _ p ((erasureCoin u hu).toMeasure.map _)
  apply (memLp_map_measure_iff
    (measurable_id.sub measurable_const).aestronglyMeasurable
    (Measurable.of_discrete : Measurable (confidenceOracle e a ρ u h x)).aemeasurable).mpr
  exact MemLp.of_discrete

theorem confidenceKernel_two_moments (e : E) (he : ‖e‖ = 1)
    {a ρ u p s L : ℝ} (ha : 0 ≤ a) (hu0 : 0 < u) (hu1 : u < 1) (hp : 0 ≤ p)
    (hs : 0 ≤ s) (hsL : s ≤ L)
    (hbudget : a ^ p * (u + u ^ p / (1 - u) ^ (p - 1)) ≤ s ^ p)
    (h : Bool) (x : E) :
    (∫ g, ‖g - ∫ z, z ∂confidenceKernel e a ρ u hu1.le h x‖ ^ p
      ∂confidenceKernel e a ρ u hu1.le h x) ≤ L ^ p ∧
    ∀ v : E, ‖v‖ = 1 →
      (∫ g, |⟪v, g - ∫ z, z ∂confidenceKernel e a ρ u hu1.le h x⟫_ℝ| ^ p
        ∂confidenceKernel e a ρ u hu1.le h x) ≤ s ^ p := by
  rw [confidenceKernel_mean e a ρ hu0.le hu1 h x]
  have hm := confidenceOracle_two_moment_admissible (ρ := ρ) e he ha hu0 hu1 hp hs hsL hbudget h x
  have hmap : Measurable (confidenceOracle e a ρ u h x) := Measurable.of_discrete
  constructor
  · change (∫ g, ‖g - confidenceMean e a ρ h x‖ ^ p
      ∂((erasureCoin u hu1.le).toMeasure.map _)) ≤ _
    have heq : (∫ g, ‖g - confidenceMean e a ρ h x‖ ^ p
        ∂((erasureCoin u hu1.le).toMeasure.map (confidenceOracle e a ρ u h x))) =
        ∫ b, ‖confidenceOracle e a ρ u h x b - confidenceMean e a ρ h x‖ ^ p
          ∂(erasureCoin u hu1.le).toMeasure :=
      integral_map hmap.aemeasurable
        ((((measurable_id : Measurable (fun g : E => g)).sub_const
          (confidenceMean e a ρ h x)).norm).pow_const p).aestronglyMeasurable
    exact heq.trans_le hm.1
  · intro v hv
    change (∫ g, |⟪v, g - confidenceMean e a ρ h x⟫_ℝ| ^ p
      ∂((erasureCoin u hu1.le).toMeasure.map _)) ≤ _
    have hcont : Continuous (fun g : E => |⟪v, g - confidenceMean e a ρ h x⟫_ℝ|) :=
      (continuous_const.inner (continuous_id.sub continuous_const)).abs
    have heq : (∫ g, |⟪v, g - confidenceMean e a ρ h x⟫_ℝ| ^ p
        ∂((erasureCoin u hu1.le).toMeasure.map (confidenceOracle e a ρ u h x))) =
        ∫ b, |⟪v, confidenceOracle e a ρ u h x b - confidenceMean e a ρ h x⟫_ℝ| ^ p
          ∂(erasureCoin u hu1.le).toMeasure :=
      integral_map hmap.aemeasurable (hcont.measurable.pow_const p).aestronglyMeasurable
    exact heq.trans_le (hm.2 v hv)

def confidencePrivateInstance (θ : OracleParameters) (e : E) (he : ‖e‖ = 1)
    (a u : ℝ) (ha : 0 ≤ a) (haG : a ≤ θ.G) (hu0 : 0 < u) (hu1 : u < 1)
    (hbudget : a ^ θ.p * (u + u ^ θ.p / (1 - u) ^ (θ.p - 1)) ≤ θ.s ^ θ.p)
    (h : Bool) : PrivateInstance (quadraticPublicProblem E θ) where
  f := confidenceLoss e a (envelopeRadius θ.μ θ.D a) h
  f_convex := confidenceLoss_convex e ha _ h
  f_lipschitz := ((confidenceLoss_lipschitz e he ha _ h).weaken haG).lipschitzOnWith
  oracle := (confidenceKernel e a (envelopeRadius θ.μ θ.D a) u hu1.le h).comap
    Subtype.val measurable_subtype_coe
  oracle_probability := by infer_instance
  reply_integrable x := confidenceKernel_integrable e a _ u hu1.le h x
  mean_subgradient x y _ := by
    change confidenceLoss e a _ h x +
      ⟪∫ g, g ∂confidenceKernel e a _ u hu1.le h x, y - (x : E)⟫_ℝ ≤ _
    rw [confidenceKernel_mean e a _ hu0.le hu1 h x, inner_sub_right]
    have hg := confidenceMean_subgradient e ha (envelopeRadius θ.μ θ.D a) h x y
    rw [inner_sub_right] at hg
    linarith only [hg]
  noise_memLp x := confidenceKernel_noise_memLp e a _ u hu1.le h x _
  strong_moment x := (confidenceKernel_two_moments e he ha hu0 hu1
    (by linarith only [θ.p_gt_one]) θ.s_pos.le θ.s_le_L hbudget h x).1
  weak_moment x := (confidenceKernel_two_moments e he ha hu0 hu1
    (by linarith only [θ.p_gt_one]) θ.s_pos.le θ.s_le_L hbudget h x).2
  minimizer := confidenceCenter e (envelopeRadius θ.μ θ.D a) h
  minimizer_domain := Set.mem_univ _
  minimizing y _ := confidenceObjective_minimizer e he θ.μ_nonneg
    (envelopeRadius_nonneg θ.μ_nonneg θ.D_pos.le ha)
    (signRadius_curvature_le θ.μ_nonneg ha) h y
  initial_distance := by
    change ‖0 - confidenceCenter e (envelopeRadius θ.μ θ.D a) h‖ ≤ θ.D
    simpa only [zero_sub, norm_neg] using
      confidenceCenter_initialization e he θ.μ_nonneg θ.D_pos.le ha h

theorem confidencePrivateInstance_loss (θ : OracleParameters) (e : E) (he : ‖e‖ = 1)
    (a u : ℝ) (ha : 0 ≤ a) (haG : a ≤ θ.G) (hu0 : 0 < u) (hu1 : u < 1)
    (hbudget : a ^ θ.p * (u + u ^ θ.p / (1 - u) ^ (θ.p - 1)) ≤ θ.s ^ θ.p)
    (h : Bool) (x : (quadraticPublicProblem E θ).X) :
    (confidencePrivateInstance θ e he a u ha haG hu0 hu1 hbudget h).loss x =
      ENNReal.ofReal (confidenceObjective e a θ.μ (envelopeRadius θ.μ θ.D a) h x -
        confidenceObjective e a θ.μ (envelopeRadius θ.μ θ.D a) h
          (confidenceCenter e (envelopeRadius θ.μ θ.D a) h)) := by
  simp only [PrivateInstance.loss, quadraticPublicProblem_S, Set.mem_univ, if_true]
  rfl

end HeavyTail
