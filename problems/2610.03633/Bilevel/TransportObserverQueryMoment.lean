import Bilevel.ProjectionPosterior
import Bilevel.TransportObserverFreshProjection
import Mathlib.MeasureTheory.Group.Integral

/-! Fresh-query moments from invariance under the stabilizer of the actually
observed subspace. This is the transcript-conditioning argument; full hard
frames are NOT conditioned on. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.TransportObserver
open EuclideanGaussian OrthogonalAction ProjectionGeometry
set_option synthInstance.maxHeartbeats 100000

theorem invariant_query_integrable (d T : ℕ) (μ : Measure (ProjectionPosterior.Frame d T))
    [IsProbabilityMeasure μ] (hnorm : ∀ᵐ U ∂μ, ∀ i, ‖U i‖ ≤ 1)
    (q : Space d) (i : Fin T) : Integrable (fun U => ⟪q,U i⟫^2) μ := by
  have hm : Measurable (fun U : ProjectionPosterior.Frame d T => ⟪q,U i⟫^2) :=
    ((continuous_const.inner (continuous_apply i)).pow 2).measurable
  apply (integrable_const (‖q‖^2)).mono' hm.aestronglyMeasurable
  filter_upwards [hnorm] with U hU
  have hh := (abs_real_inner_le_norm q (U i)).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hU i) (norm_nonneg q))
  have hs := pow_le_pow_left₀ (abs_nonneg _) hh 2
  simpa only [Real.norm_eq_abs,abs_pow,sq_abs] using hs

/-- Residual coordinate second moments agree under the actual stabilizer
invariance of a posterior frame law. No independent-column hypothesis occurs. -/
theorem invariant_query_coordinate_eq (d T : ℕ) (V : Submodule ℝ (Space d))
    (μ : Measure (ProjectionPosterior.Frame d T))
    (hμ : ProjectionPosterior.Invariant d T V μ)
    (x y : Space d) (hx : x ∈ Vᗮ) (hy : y ∈ Vᗮ) (hn : ‖x‖ = ‖y‖) (i : Fin T) :
    (∫ U, ⟪x,U i⟫^2 ∂μ) = ∫ U, ⟪y,U i⟫^2 ∂μ := by
  obtain ⟨A,hA⟩ := ProjectionStabilizer.transitive_on_residual_sphere d V x y hx hy hn
  have hi (U : ProjectionPosterior.Frame d T) : ⟪y,(A • U) i⟫ = ⟪x,U i⟫ := by
    change ⟪y,A.val • U i⟫ = ⟪x,U i⟫
    rw [← hA]
    exact (isometry d A.val).inner_map_map x (U i)
  calc
    _ = ∫ U, ⟪y,(A • U) i⟫^2 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun U => congrArg (fun z : ℝ => z^2) (hi U).symm)
    _ = _ := (hμ A).integral_comp (MeasurableEquiv.smul A).measurableEmbedding
      (fun U : ProjectionPosterior.Frame d T => ⟪y,U i⟫^2)

theorem invariant_query_column_moment {ι : Type*} [Fintype ι]
    (d T : ℕ) (V : Submodule ℝ (Space d)) (b : OrthonormalBasis ι ℝ Vᗮ)
    (hd : 0 < Fintype.card ι) (μ : Measure (ProjectionPosterior.Frame d T))
    [IsProbabilityMeasure μ] (hμ : ProjectionPosterior.Invariant d T V μ)
    (hnorm : ∀ᵐ U ∂μ, ∀ i, ‖U i‖ ≤ 1)
    (q : Space d) (hqV : q ∈ Vᗮ) (hq : ‖q‖ = 1) (i : Fin T) :
    (∫ U, ⟪q,U i⟫^2 ∂μ) ≤ 1/(Fintype.card ι : ℝ) := by
  have hi (j : ι) := invariant_query_integrable d T μ hnorm (b j : Space d) i
  have he (j : ι) : (∫ U, ⟪(b j : Space d),U i⟫^2 ∂μ) = ∫ U, ⟪q,U i⟫^2 ∂μ :=
    invariant_query_coordinate_eq d T V μ hμ _ q (b j).property hqV
      ((b.orthonormal.norm_eq_one j).trans hq.symm) i
  have hs : ∀ᵐ U ∂μ, (∑ j, ⟪(b j : Space d),U i⟫^2) ≤ (1:ℝ) := by
    filter_upwards [hnorm] with U hU
    have hh := (b.orthonormal.comp_linearIsometry Vᗮ.subtypeₗᵢ).sum_inner_products_le
      (s := Finset.univ) (U i)
    have hh' : (∑ j, ⟪(b j : Space d),U i⟫^2) ≤ ‖U i‖^2 := by
      simpa only [Function.comp_apply,Submodule.coe_subtypeₗᵢ,Real.norm_eq_abs,sq_abs] using hh
    exact hh'.trans (by nlinarith [norm_nonneg (U i),hU i])
  have hb := integral_mono_ae (integrable_finset_sum _ (fun j _ => hi j))
    (integrable_const (1:ℝ)) hs
  rw [integral_finset_sum _ (fun j _ => hi j)] at hb
  simp_rw [he] at hb
  have hb' : (Fintype.card ι : ℝ)*(∫ U, ⟪q,U i⟫^2 ∂μ) ≤ 1 := by simpa using hb
  apply (le_div_iff₀ (by exact_mod_cast hd : (0:ℝ) < Fintype.card ι)).mpr
  simpa only [mul_comm] using hb'

/-- The total moment of one actual unit query innovation against all T
columns is at most T divided by the unobserved dimension. -/
theorem invariant_query_total_moment {ι : Type*} [Fintype ι]
    (d T : ℕ) (V : Submodule ℝ (Space d)) (b : OrthonormalBasis ι ℝ Vᗮ)
    (hd : 0 < Fintype.card ι) (μ : Measure (ProjectionPosterior.Frame d T))
    [IsProbabilityMeasure μ] (hμ : ProjectionPosterior.Invariant d T V μ)
    (hnorm : ∀ᵐ U ∂μ, ∀ i, ‖U i‖ ≤ 1)
    (q : Space d) (hqV : q ∈ Vᗮ) (hq : ‖q‖ = 1) :
    (∫ U, ∑ i, ⟪q,U i⟫^2 ∂μ) ≤ (T:ℝ)/(Fintype.card ι : ℝ) := by
  rw [integral_finset_sum _ (fun i _ => invariant_query_integrable d T μ hnorm q i)]
  calc
    _ ≤ ∑ _i : Fin T, (1:ℝ)/(Fintype.card ι : ℝ) :=
      Finset.sum_le_sum (fun i _ => invariant_query_column_moment d T V b hd μ hμ hnorm q hqV hq i)
    _ = _ := by simp [div_eq_mul_inv]

end Bilevel.TransportObserver
