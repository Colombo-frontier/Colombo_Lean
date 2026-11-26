import Bilevel.TransportNetworkStabilizer
import Bilevel.TransportObserverQueryPosterior
import Bilevel.TransportObserverDimensions

/-! Query-side moment bounds for the ACTUAL latent network law and every
posterior that retains its layerwise gauge invariance. No conditioning on
full hard frames is used. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.TransportNetwork
open EuclideanGaussian
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 500000

theorem physical_frame_invariant {n d : ℕ} (T : ℕ) (hT : T ≤ d)
    (W : Known n d) (μ : Measure (Latent n d)) (hμ : Invariant W μ) (v : Vertex n) :
    ProjectionPosterior.Invariant d T (W v) (μ.map (fun z => frame T hT z v)) := by
  intro A
  let R : LocalGauge W := fun w => if h : w = v then h.symm ▸ A else 1
  have hRv : (R v).val = A.val := by simp only [R,dif_pos rfl]
  have hm : Measurable (fun z : Latent n d => frame T hT z v) :=
    (measurable_pi_apply v).comp (frame_measurable n d T hT)
  apply ConditionalSymmetry.pushforward_preserving μ _ hm (fun z => R • z)
    (fun U : ProjectionPosterior.Frame d T => A • U) (hμ R)
    (measurable_const.smul measurable_id)
  intro z
  funext i
  change frame T hT (gauge (lift R) z) v i = A.val • frame T hT z v i
  rw [frame_gauge]
  change (R v).val • frame T hT z v i = _
  rw [hRv]

theorem physical_frame_norm_ae {n d : ℕ} (T : ℕ) (hT : T ≤ d)
    (μ : Measure (Latent n d)) (v : Vertex n) :
    ∀ᵐ U ∂μ.map (fun z => frame T hT z v), ∀ i, ‖U i‖ ≤ 1 := by
  have hm : Measurable (fun z : Latent n d => frame T hT z v) :=
    (measurable_pi_apply v).comp (frame_measurable n d T hT)
  apply (ae_map_iff hm.aemeasurable (TransportObserver.frame_norm_set_measurable d T)).mpr
  exact Filter.Eventually.of_forall (fun z i => (frame_orthonormal T hT z v).norm_eq_one i |>.le)

theorem query_total_moment {n d ι : ℕ} (T : ℕ) (hT : T ≤ d)
    (W : Known n d) (μ : Measure (Latent n d)) [IsProbabilityMeasure μ]
    (hμ : Invariant W μ) (v : Vertex n)
    (b : OrthonormalBasis (Fin ι) ℝ (W v)ᗮ) (hd : 0 < ι)
    (q : Space d) (hqV : q ∈ (W v)ᗮ) (hq : ‖q‖ = 1) :
    (∫ z, ∑ i, ⟪q,frame T hT z v i⟫^2 ∂μ) ≤ (T:ℝ)/(ι:ℝ) := by
  let f := fun z : Latent n d => frame T hT z v
  have hm : Measurable f := (measurable_pi_apply v).comp (frame_measurable n d T hT)
  letI : IsProbabilityMeasure (μ.map f) := isProbabilityMeasure_map hm.aemeasurable
  have hh := TransportObserver.invariant_query_total_moment d T (W v) b
    (by simpa only [Fintype.card_fin] using hd) (μ.map f)
    (physical_frame_invariant T hT W μ hμ v) (physical_frame_norm_ae T hT μ v) q hqV hq
  have hg : Measurable (fun U : ProjectionPosterior.Frame d T => ∑ i, ⟪q,U i⟫^2) :=
    Finset.measurable_sum _ (fun i _ =>
      ((continuous_const.inner (continuous_apply i)).pow 2).measurable)
  rw [integral_map hm.aemeasurable hg.aestronglyMeasurable] at hh
  simpa only [Fintype.card_fin] using hh

theorem query_statistic_integrable {n d : ℕ} (T : ℕ) (hT : T ≤ d)
    (μ : Measure (Latent n d)) [IsProbabilityMeasure μ] (v : Vertex n) (q : Space d) :
    Integrable (fun z => ∑ i, ⟪q,frame T hT z v i⟫^2) μ := by
  let f := fun z : Latent n d => frame T hT z v
  have hm : Measurable f := (measurable_pi_apply v).comp (frame_measurable n d T hT)
  letI : IsProbabilityMeasure (μ.map f) := isProbabilityMeasure_map hm.aemeasurable
  have hh := integrable_finset_sum Finset.univ (fun i _ =>
    TransportObserver.invariant_query_integrable d T (μ.map f) (physical_frame_norm_ae T hT μ v) q i)
  exact hh.comp_measurable hm

theorem query_failure_dimension {n D : ℕ} (T : ℕ) (hT : T ≤ D)
    (W : Known n D) (μ : Measure (Latent n D)) [IsProbabilityMeasure μ]
    (hμ : Invariant W μ) (v : Vertex n) (d : ℕ)
    (hW : Module.finrank ℝ (W v) ≤ d) (hd : d < D)
    (q : Space D) (hqV : q ∈ (W v)ᗮ) (hq : ‖q‖ = 1) (a : ℝ) (ha : 0 < a) :
    μ.real {z | a < ∑ i, ⟪q,frame T hT z v i⟫^2} ≤ (T:ℝ)/(((D:ℝ)-d)*a) := by
  have hr := TransportObserver.residual_dimension_real D (W v)
  have hDr : (d:ℝ) < D := by exact_mod_cast hd
  have hWr : (Module.finrank ℝ (W v) : ℝ) ≤ d := by exact_mod_cast hW
  have hres : 0 < Module.finrank ℝ (W v)ᗮ := by
    have hh : (0:ℝ) < (Module.finrank ℝ (W v)ᗮ : ℝ) := by linarith
    exact_mod_cast hh
  have hm := (mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (Filter.Eventually.of_forall (fun z => Finset.sum_nonneg (fun i _ =>
      sq_nonneg ⟪q,frame T hT z v i⟫))) (query_statistic_integrable T hT μ v q) a).trans
    (query_total_moment T hT W μ hμ v (stdOrthonormalBasis ℝ (W v)ᗮ) hres q hqV hq)
  have hp : μ.real {z | a ≤ ∑ i, ⟪q,frame T hT z v i⟫^2} ≤
      ((T:ℝ)/(Module.finrank ℝ (W v)ᗮ : ℝ))/a :=
    (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hm)
  have hsub : {z : Latent n D | a < ∑ i, ⟪q,frame T hT z v i⟫^2} ⊆
      {z | a ≤ ∑ i, ⟪q,frame T hT z v i⟫^2} := by
    intro z hz
    change a < ∑ i, ⟪q,frame T hT z v i⟫^2 at hz
    change a ≤ ∑ i, ⟪q,frame T hT z v i⟫^2
    exact hz.le
  have hb := (measureReal_mono (μ := μ) hsub).trans hp
  rw [div_div] at hb
  exact hb.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg T) (mul_pos (by linarith) ha)
    (mul_le_mul_of_nonneg_right (by linarith : (D:ℝ)-d ≤ (Module.finrank ℝ (W v)ᗮ : ℝ)) ha.le))

end Bilevel.TransportNetwork
