import Bilevel.TransportObserverQueryMoment
import Bilevel.TransportObserverHaarMoment

/-! The fresh complementary Frobenius moment follows from actual residual
isotropy and support. Identifying a posterior with a separately sampled Haar
matrix is unnecessary; its proved stabilizer invariance suffices. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.TransportObserver
open EuclideanGaussian ProjectionGeometry
set_option maxHeartbeats 400000

theorem invariant_residual_vector_moment {ι : Type*} [Fintype ι]
    (D T : ℕ) (B : Submodule ℝ (Space D)) (b : OrthonormalBasis ι ℝ Bᗮ)
    (hd : 0 < Fintype.card ι) (μ : Measure (ProjectionPosterior.Frame D T))
    [IsProbabilityMeasure μ] (hμ : ProjectionPosterior.Invariant D T B μ)
    (hnorm : ∀ᵐ U ∂μ, ∀ i, ‖U i‖ ≤ 1)
    (v : Space D) (hv : v ∈ Bᗮ) (i : Fin T) :
    (∫ U, ⟪v,U i⟫^2 ∂μ) ≤ ‖v‖^2/(Fintype.card ι : ℝ) := by
  by_cases hzero : v = 0
  · simp [hzero]
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hzero
    let q := ‖v‖⁻¹ • v
    have hqB : q ∈ Bᗮ := Bᗮ.smul_mem _ hv
    have hq : ‖q‖ = 1 := by
      simp only [q,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg v),inv_mul_cancel₀ hn]
    have hrec : ‖v‖ • q = v := by simp only [q,smul_smul,mul_inv_cancel₀ hn,one_smul]
    have hi (U : ProjectionPosterior.Frame D T) : ⟪v,U i⟫ = ‖v‖*⟪q,U i⟫ := by
      rw [← real_inner_smul_left,hrec]
    have he : (∫ U, ⟪v,U i⟫^2 ∂μ) = ‖v‖^2*(∫ U, ⟪q,U i⟫^2 ∂μ) := by
      simp_rw [hi,mul_pow]
      exact integral_const_mul _ _
    rw [he]
    have hh := mul_le_mul_of_nonneg_left
      (invariant_query_column_moment D T B b hd μ hμ hnorm q hqB hq i) (sq_nonneg ‖v‖)
    simpa only [mul_one_div] using hh

theorem invariant_supported_inner_moment {ι : Type*} [Fintype ι]
    (D T : ℕ) (B : Submodule ℝ (Space D)) (b : OrthonormalBasis ι ℝ Bᗮ)
    (hd : 0 < Fintype.card ι) (μ : Measure (ProjectionPosterior.Frame D T))
    [IsProbabilityMeasure μ] (hμ : ProjectionPosterior.Invariant D T B μ)
    (hnorm : ∀ᵐ U ∂μ, ∀ i, ‖U i‖ ≤ 1)
    (hperp : ∀ᵐ U ∂μ, ∀ i, U i ∈ Bᗮ) (w : Space D) (i : Fin T) :
    (∫ U, ⟪w,U i⟫^2 ∂μ) ≤ ‖w‖^2/(Fintype.card ι : ℝ) := by
  have he : (fun U : ProjectionPosterior.Frame D T => ⟪w,U i⟫^2) =ᵐ[μ]
      (fun U => ⟪ProjectionGeometry.residual B w,U i⟫^2) := by
    filter_upwards [hperp] with U hU
    rw [ProjectionGeometry.residual,inner_sub_left,
      Submodule.inner_right_of_mem_orthogonal (project_mem B w) (hU i),sub_zero]
  rw [integral_congr_ae he]
  have hh := invariant_residual_vector_moment D T B b hd μ hμ hnorm
    (ProjectionGeometry.residual B w) (Submodule.sub_orthogonalProjection_mem_orthogonal w) i
  exact hh.trans (div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (residual_norm_le B w) 2) (Nat.cast_nonneg _))

theorem invariant_supported_projection_moment {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D T : ℕ) (B W : Submodule ℝ (Space D)) (b : OrthonormalBasis ι ℝ Bᗮ)
    (bW : OrthonormalBasis κ ℝ W) (hd : 0 < Fintype.card ι)
    (μ : Measure (ProjectionPosterior.Frame D T)) [IsProbabilityMeasure μ]
    (hμ : ProjectionPosterior.Invariant D T B μ)
    (hnorm : ∀ᵐ U ∂μ, ∀ i, ‖U i‖ ≤ 1) (hperp : ∀ᵐ U ∂μ, ∀ i, U i ∈ Bᗮ)
    (i : Fin T) :
    (∫ U, energy W (U i) ∂μ) ≤ (Fintype.card κ : ℝ)/(Fintype.card ι : ℝ) := by
  simp_rw [projection_energy_parseval W bW]
  rw [integral_finset_sum _ (fun j _ => invariant_query_integrable D T μ hnorm (bW j : Space D) i)]
  calc
    _ ≤ ∑ _j : κ, (1:ℝ)/(Fintype.card ι : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      have hh := invariant_supported_inner_moment D T B b hd μ hμ hnorm hperp (bW j : Space D) i
      have hn : ‖(bW j : Space D)‖ = 1 := bW.orthonormal.norm_eq_one j
      simpa only [hn,one_pow] using hh
    _ = _ := by simp [div_eq_mul_inv]

theorem invariant_supported_frame_moment {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D T : ℕ) (B W : Submodule ℝ (Space D)) (b : OrthonormalBasis ι ℝ Bᗮ)
    (bW : OrthonormalBasis κ ℝ W) (hd : 0 < Fintype.card ι)
    (μ : Measure (ProjectionPosterior.Frame D T)) [IsProbabilityMeasure μ]
    (hμ : ProjectionPosterior.Invariant D T B μ)
    (hnorm : ∀ᵐ U ∂μ, ∀ i, ‖U i‖ ≤ 1) (hperp : ∀ᵐ U ∂μ, ∀ i, U i ∈ Bᗮ) :
    (∫ U, frameEnergy W U Finset.univ ∂μ) ≤ (T:ℝ)*Fintype.card κ/(Fintype.card ι : ℝ) := by
  have hi (i : Fin T) : Integrable (fun U => energy W (U i)) μ := by
    simp_rw [projection_energy_parseval W bW]
    exact integrable_finset_sum _ (fun j _ => invariant_query_integrable D T μ hnorm (bW j : Space D) i)
  unfold frameEnergy
  rw [integral_finset_sum _ (fun i _ => hi i)]
  calc
    _ ≤ ∑ _i : Fin T, (Fintype.card κ : ℝ)/(Fintype.card ι : ℝ) :=
      Finset.sum_le_sum (fun i _ => invariant_supported_projection_moment D T B W b bW hd μ hμ hnorm hperp i)
    _ = _ := by simp [div_eq_mul_inv,mul_assoc]

end Bilevel.TransportObserver
