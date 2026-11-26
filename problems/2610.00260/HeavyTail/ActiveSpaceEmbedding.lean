import HeavyTail.OracleQuadratic
import HeavyTail.HardFamily
import HeavyTail.GaussianMomentModel
import HeavyTail.GaussianAdaptiveSampler
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Kernel.Composition.MapComap

/-! Active-space lower instances embedded into the full ambient quadratic
problem. The public regularizer is the full ambient squared norm. The oracle
kernel is genuinely pushed forward through a linear isometry, with all model
fields and objective domination derived from the active instance. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
namespace HeavyTail

section Geometry
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def activeProjection (e : E →ₗᵢ[ℝ] F) : F →L[ℝ] E := e.toContinuousLinearMap.adjoint

theorem activeProjection_inner (e : E →ₗᵢ[ℝ] F) (x : E) (y : F) :
    ⟪activeProjection e y, x⟫_ℝ = ⟪y, e x⟫_ℝ :=
  e.toContinuousLinearMap.adjoint_inner_left x y

theorem activeProjection_embed (e : E →ₗᵢ[ℝ] F) (x : E) : activeProjection e (e x) = x := by
  apply ext_inner_right ℝ
  intro y
  rw [activeProjection_inner, e.inner_map_map]

theorem activeProjection_norm_le (e : E →ₗᵢ[ℝ] F) (y : F) : ‖activeProjection e y‖ ≤ ‖y‖ := by
  have hi := activeProjection_inner e (activeProjection e y) y
  rw [real_inner_self_eq_norm_sq] at hi
  have hc := real_inner_le_norm y (e (activeProjection e y))
  rw [e.norm_map, ← hi] at hc
  nlinarith [norm_nonneg (activeProjection e y), norm_nonneg y]

theorem activeProjection_lipschitz (e : E →ₗᵢ[ℝ] F) : LipschitzWith 1 (activeProjection e) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub]
  exact activeProjection_norm_le e (x - y)

end Geometry

/-- The first k standard basis vectors of the ambient d-dimensional space
give a concrete isometric embedding whenever k≤d. -/
def firstCoordinatesEmbedding {k d : ℕ} (hkd : k ≤ d) : HardSpace k →ₗᵢ[ℝ] HardSpace d := by
  let b : Basis (Fin k) ℝ (HardSpace k) := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let c : Fin k → HardSpace d := fun i => EuclideanSpace.basisFun (Fin d) ℝ (Fin.castLE hkd i)
  let f : HardSpace k →ₗ[ℝ] HardSpace d := b.constr ℝ c
  have hc : Orthonormal ℝ c :=
    (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.comp (Fin.castLE hkd) (Fin.castLE_injective hkd)
  have hf : Orthonormal ℝ (f ∘ b) := by
    have he : f ∘ b = c := by funext i; exact b.constr_basis ℝ c i
    rw [he]
    exact hc
  exact f.isometryOfOrthonormal (v := b) (EuclideanSpace.basisFun (Fin k) ℝ).orthonormal hf

section Model
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
  {θ : OracleParameters}

def activeQuery (e : E →ₗᵢ[ℝ] F) (x : (quadraticPublicProblem F θ).X) :
    (quadraticPublicProblem E θ).X := ⟨activeProjection e x, Set.mem_univ _⟩

theorem activeQuery_measurable (e : E →ₗᵢ[ℝ] F) : Measurable (activeQuery (θ := θ) e) :=
  ((activeProjection e).continuous.measurable.comp measurable_subtype_coe).subtype_mk

def embeddedOracle (e : E →ₗᵢ[ℝ] F) (I : PrivateInstance (quadraticPublicProblem E θ)) :
    Kernel (quadraticPublicProblem F θ).X F :=
  (I.oracle.comap (activeQuery e) (activeQuery_measurable e)).map e

theorem embeddedOracle_apply (e : E →ₗᵢ[ℝ] F) (I : PrivateInstance (quadraticPublicProblem E θ))
    (x : (quadraticPublicProblem F θ).X) :
    embeddedOracle e I x = (I.oracle (activeQuery e x)).map e :=
  Kernel.map_apply _ e.continuous.measurable x

/-- A concrete active sampler remains a concrete fresh sampler after embedding;
this identity connects arbitrary-seed adaptive testing to the lifted instance. -/
theorem embeddedOracle_sampler {N : Type*} [MeasurableSpace N]
    (e : E →ₗᵢ[ℝ] F) (I : PrivateInstance (quadraticPublicProblem E θ))
    (ν : Measure N) [IsProbabilityMeasure ν] (f : E × N → E) (hf : Measurable f)
    (hI : I.oracle = (kernelOfSampler ν f hf).comap Subtype.val measurable_subtype_coe) :
    embeddedOracle e I = kernelOfSampler ν
      (fun z : (quadraticPublicProblem F θ).X × N =>
        e (f (activeProjection e z.1, z.2)))
      (e.continuous.measurable.comp (hf.comp
        (((activeProjection e).continuous.measurable.comp
          (measurable_subtype_coe.comp measurable_fst)).prodMk measurable_snd))) := by
  ext x S hS
  rw [embeddedOracle_apply, hI, Kernel.comap_apply, kernelOfSampler_apply,
    kernelOfSampler_apply]
  have heq := Measure.map_map (μ := ν) e.continuous.measurable
    (hf.comp (measurable_prodMk_left : Measurable (fun z : N => (activeProjection e x, z))))
  exact congrArg (fun μ : Measure F => μ S) heq

instance embeddedOracle_markov (e : E →ₗᵢ[ℝ] F) (I : PrivateInstance (quadraticPublicProblem E θ)) :
    IsMarkovKernel (embeddedOracle e I) :=
  Kernel.IsMarkovKernel.map _ e.continuous.measurable

theorem embeddedOracle_integrable (e : E →ₗᵢ[ℝ] F) (I : PrivateInstance (quadraticPublicProblem E θ))
    (x : (quadraticPublicProblem F θ).X) : Integrable (fun g : F => g) (embeddedOracle e I x) := by
  rw [embeddedOracle_apply]
  apply (integrable_map_measure measurable_id.aestronglyMeasurable e.continuous.measurable.aemeasurable).mpr
  exact e.toContinuousLinearMap.integrable_comp (I.reply_integrable (activeQuery e x))

theorem embeddedOracle_mean (e : E →ₗᵢ[ℝ] F) (I : PrivateInstance (quadraticPublicProblem E θ))
    (x : (quadraticPublicProblem F θ).X) :
    (∫ g, g ∂embeddedOracle e I x) = e (I.mean (activeQuery e x)) := by
  rw [embeddedOracle_apply]
  calc
    _ = ∫ g, e g ∂I.oracle (activeQuery e x) :=
      integral_map e.continuous.measurable.aemeasurable
        (measurable_id : Measurable (fun g : F => g)).aestronglyMeasurable
    _ = _ := e.integral_comp_comm (fun g => g)

theorem embeddedOracle_noise_memLp (e : E →ₗᵢ[ℝ] F)
    (I : PrivateInstance (quadraticPublicProblem E θ)) (x : (quadraticPublicProblem F θ).X) :
    MemLp (fun g => g - ∫ z, z ∂embeddedOracle e I x) (ENNReal.ofReal θ.p) (embeddedOracle e I x) := by
  rw [embeddedOracle_mean, embeddedOracle_apply]
  apply (memLp_map_measure_iff
    ((measurable_id : Measurable (fun g : F => g)).sub_const _).aestronglyMeasurable
    e.continuous.measurable.aemeasurable).mpr
  apply (I.noise_memLp (activeQuery e x)).congr_norm
  · exact (e.continuous.measurable.sub_const _).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun g => by
      change ‖g - I.mean (activeQuery e x)‖ = ‖e g - e (I.mean (activeQuery e x))‖
      rw [← e.map_sub, e.norm_map]

theorem embeddedOracle_strong_moment (e : E →ₗᵢ[ℝ] F)
    (I : PrivateInstance (quadraticPublicProblem E θ)) (x : (quadraticPublicProblem F θ).X) :
    (∫ g, ‖g - ∫ z, z ∂embeddedOracle e I x‖ ^ θ.p ∂embeddedOracle e I x) ≤ θ.L ^ θ.p := by
  rw [embeddedOracle_mean, embeddedOracle_apply]
  have hm : Measurable (fun g : F => ‖g - e (I.mean (activeQuery e x))‖ ^ θ.p) :=
    (((measurable_id : Measurable (fun g : F => g)).sub_const _).norm).pow_const _
  have heq := integral_map (μ := I.oracle (activeQuery e x))
    e.continuous.measurable.aemeasurable hm.aestronglyMeasurable
  rw [heq]
  simp only [← e.map_sub, e.norm_map]
  exact I.strong_moment (activeQuery e x)

theorem embeddedOracle_weak_moment (e : E →ₗᵢ[ℝ] F)
    (I : PrivateInstance (quadraticPublicProblem E θ)) (x : (quadraticPublicProblem F θ).X)
    (v : F) (hv : ‖v‖ = 1) :
    (∫ g, |⟪v, g - ∫ z, z ∂embeddedOracle e I x⟫_ℝ| ^ θ.p ∂embeddedOracle e I x) ≤ θ.s ^ θ.p := by
  rw [embeddedOracle_mean, embeddedOracle_apply]
  have hc : Continuous (fun g : F => |⟪v, g - e (I.mean (activeQuery e x))⟫_ℝ|) :=
    (continuous_const.inner (continuous_id.sub continuous_const)).abs
  have heq := integral_map (μ := I.oracle (activeQuery e x))
    e.continuous.measurable.aemeasurable (hc.measurable.pow_const θ.p).aestronglyMeasurable
  rw [heq]
  simp only [← e.map_sub, ← activeProjection_inner]
  have hbound := GaussianEstimates.unit_direction_bound E
    (ξ := fun g => g - I.mean (activeQuery e x))
    (by linarith only [θ.p_gt_one] : 0 < θ.p) θ.s_pos.le
    (I.weak_moment (activeQuery e x)) (activeProjection e v)
  apply hbound.trans
  apply Real.rpow_le_rpow (mul_nonneg θ.s_pos.le (norm_nonneg _)) _
    (by linarith only [θ.p_gt_one])
  calc
    θ.s * ‖activeProjection e v‖ ≤ θ.s * ‖v‖ :=
      mul_le_mul_of_nonneg_left (activeProjection_norm_le e v) θ.s_pos.le
    _ = θ.s := by rw [hv, mul_one]

theorem embedded_objective_domination (e : E →ₗᵢ[ℝ] F)
    (I : PrivateInstance (quadraticPublicProblem E θ)) (y : F) :
    I.f (activeProjection e y) + θ.μ / 2 * ‖activeProjection e y‖ ^ 2 ≤
      I.f (activeProjection e y) + θ.μ / 2 * ‖y‖ ^ 2 := by
  have hn := activeProjection_norm_le e y
  have hs : ‖activeProjection e y‖ ^ 2 ≤ ‖y‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  exact add_le_add_left (mul_le_mul_of_nonneg_left hs (div_nonneg θ.μ_nonneg (by norm_num))) _

theorem embedded_objective_minimizer (e : E →ₗᵢ[ℝ] F)
    (I : PrivateInstance (quadraticPublicProblem E θ)) (y : F) :
    I.f (activeProjection e (e I.minimizer)) + θ.μ / 2 * ‖e I.minimizer‖ ^ 2 ≤
      I.f (activeProjection e y) + θ.μ / 2 * ‖y‖ ^ 2 := by
  rw [activeProjection_embed, e.norm_map]
  exact (I.minimizing (activeProjection e y) (Set.mem_univ _)).trans
    (embedded_objective_domination e I y)

def embeddedPrivateInstance (e : E →ₗᵢ[ℝ] F) (I : PrivateInstance (quadraticPublicProblem E θ)) :
    PrivateInstance (quadraticPublicProblem F θ) where
  f y := I.f (activeProjection e y)
  f_convex := by
    have hf := I.f_convex.comp_linearMap (activeProjection e).toLinearMap
    simpa only [quadraticPublicProblem_X, Set.preimage_univ, Function.comp_def,
      ContinuousLinearMap.coe_coe] using hf
  f_lipschitz := by
    have hf : LipschitzWith ⟨θ.G, θ.G_pos.le⟩ I.f := lipschitzOnWith_univ.mp I.f_lipschitz
    have hcomp := hf.comp (activeProjection_lipschitz e)
    simpa only [mul_one] using hcomp.lipschitzOnWith (s := Set.univ)
  oracle := embeddedOracle e I
  oracle_probability := by infer_instance
  reply_integrable := embeddedOracle_integrable e I
  mean_subgradient x y _ := by
    rw [embeddedOracle_mean]
    have hi : ⟪e (I.mean (activeQuery e x)), y - (x : F)⟫_ℝ =
        ⟪I.mean (activeQuery e x), activeProjection e y - activeProjection e x⟫_ℝ := by
      calc
        _ = ⟪I.mean (activeQuery e x), activeProjection e (y - (x : F))⟫_ℝ :=
          (e.toContinuousLinearMap.adjoint_inner_right (I.mean (activeQuery e x)) (y - (x : F))).symm
        _ = _ := by rw [map_sub]
    rw [hi]
    exact I.mean_subgradient (activeQuery e x) (activeProjection e y) (Set.mem_univ _)
  noise_memLp := embeddedOracle_noise_memLp e I
  strong_moment := embeddedOracle_strong_moment e I
  weak_moment := embeddedOracle_weak_moment e I
  minimizer := e I.minimizer
  minimizer_domain := Set.mem_univ _
  minimizing y _ := embedded_objective_minimizer e I y
  initial_distance := by
    change ‖0 - e I.minimizer‖ ≤ θ.D
    rw [zero_sub, norm_neg, e.norm_map]
    simpa only [quadraticPublicProblem_initial, zero_sub, norm_neg] using I.initial_distance

@[simp] theorem embeddedPrivateInstance_oracle (e : E →ₗᵢ[ℝ] F)
    (I : PrivateInstance (quadraticPublicProblem E θ)) :
    (embeddedPrivateInstance e I).oracle = embeddedOracle e I := rfl

theorem embeddedPrivateInstance_optimalValue (e : E →ₗᵢ[ℝ] F)
    (I : PrivateInstance (quadraticPublicProblem E θ)) :
    (embeddedPrivateInstance e I).optimalValue = I.optimalValue := by
  change I.f (activeProjection e (e I.minimizer)) + θ.μ / 2 * ‖e I.minimizer‖ ^ 2 = _
  rw [activeProjection_embed, e.norm_map]
  rfl

theorem embeddedPrivateInstance_loss_domination (e : E →ₗᵢ[ℝ] F)
    (I : PrivateInstance (quadraticPublicProblem E θ)) (x : (quadraticPublicProblem F θ).X) :
    I.loss (activeQuery e x) ≤ (embeddedPrivateInstance e I).loss x := by
  rw [I.loss_of_mem _ (Set.mem_univ _),
    (embeddedPrivateInstance e I).loss_of_mem _ (Set.mem_univ _), embeddedPrivateInstance_optimalValue]
  apply ENNReal.ofReal_le_ofReal
  exact sub_le_sub_right (embedded_objective_domination e I x) _

end Model
end HeavyTail
