import Nonsmooth.GaussianAxisDecomposition

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

theorem negative_quadratic_slice_interval {b t : ℝ} (hb : b ≤ 0) (ht : 0 ≤ t) :
    {x : ℝ | x ^ 2 ≤ t ∧ x ≤ b} = Icc (-Real.sqrt t) b := by
  ext x
  have hs := Real.sq_sqrt ht
  have hp := Real.sqrt_nonneg t
  constructor
  · intro hx
    exact ⟨by nlinarith [hx.1, hx.2], hx.2⟩
  · intro hx
    exact ⟨by nlinarith [hx.1, hx.2], hx.2⟩

theorem standardGaussian_negative_quadratic_slice (c R : ℝ) {b : ℝ} (hb : b ≤ 0) :
    (∫ x in {x : ℝ | x ^ 2 + c ≤ R ^ 2 ∧ x ≤ b}, (x - b) ^ 2 ∂gaussianReal 0 1) ≤
      (gaussianReal 0 1).real {x : ℝ | x ^ 2 + c ≤ R ^ 2 ∧ x ≤ b} := by
  have he : {x : ℝ | x ^ 2 + c ≤ R ^ 2 ∧ x ≤ b} =
      {x : ℝ | x ^ 2 ≤ R ^ 2 - c ∧ x ≤ b} := by
    ext x
    simp only [mem_setOf_eq, le_sub_iff_add_le]
  rw [he]
  by_cases ht : 0 ≤ R ^ 2 - c
  · rw [negative_quadratic_slice_interval hb ht]
    exact standardGaussian_left_interval_second _ hb
  · have hz : {x : ℝ | x ^ 2 ≤ R ^ 2 - c ∧ x ≤ b} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      nlinarith [hx.1, sq_nonneg x]
    simp [hz]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussian_axis_cap_geometry {u : E} (hu : ‖u‖ = 1) {z : E} (hz : z ∈ (ℝ ∙ u)ᗮ)
    (x R b : ℝ) :
    (‖x • u + z‖ ^ 2 ≤ R ^ 2 ∧ ⟪x • u + z, u⟫_ℝ ≤ b) ↔
      (x ^ 2 + ‖z‖ ^ 2 ≤ R ^ 2 ∧ x ≤ b) := by
  have hi : ⟪u, z⟫_ℝ = 0 :=
    (Submodule.mem_orthogonal _ _).mp hz u (Submodule.mem_span_singleton_self u)
  have hz' : ⟪z, u⟫_ℝ = 0 := by rw [real_inner_comm, hi]
  have hs : ⟪x • u, z⟫_ℝ = 0 := by rw [real_inner_smul_left, hi, mul_zero]
  have hn : ‖x • u + z‖ ^ 2 = ‖x • u‖ ^ 2 + ‖z‖ ^ 2 := by
    nlinarith [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hs]
  rw [hn,
    norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs,
    inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hu, hz']
  norm_num

/-- Negative spherical caps of the raw Gaussian have squared axial distance to
their boundary bounded by their mass. This is an unnormalized statement. -/
theorem euclideanGaussian_negative_cap_second {u : E} (hu : ‖u‖ = 1) (R : ℝ)
    {b : ℝ} (hb : b ≤ 0) :
    (∫ z in {z : E | ‖z‖ ^ 2 ≤ R ^ 2 ∧ ⟪z, u⟫_ℝ ≤ b}, (⟪z, u⟫_ℝ - b) ^ 2
      ∂euclideanGaussianLaw E) ≤
        (euclideanGaussianLaw E).real {z : E | ‖z‖ ^ 2 ≤ R ^ 2 ∧ ⟪z, u⟫_ℝ ≤ b} := by
  let A : Set E := {z : E | ‖z‖ ^ 2 ≤ R ^ 2 ∧ ⟪z, u⟫_ℝ ≤ b}
  let F : E × ℝ → E := fun p => p.2 • u + p.1
  let Q := (gaussianOrthogonalResidualLaw (ℝ ∙ u)).prod (gaussianReal 0 1)
  let g : E → ℝ := A.indicator (fun z => (⟪z, u⟫_ℝ - b) ^ 2)
  let h : E → ℝ := A.indicator (fun _ => 1)
  have hproj : Measurable (fun z : E => ⟪z, u⟫_ℝ) :=
    (continuous_id.inner continuous_const).measurable
  have hA : MeasurableSet A :=
    (measurableSet_le (continuous_norm.pow 2).measurable measurable_const).inter
      (measurableSet_le hproj measurable_const)
  have hF : Measurable F := by fun_prop
  have hQ : Q.map F = euclideanGaussianLaw E := euclideanGaussian_axis_reconstruction hu
  have hraw : MemLp (fun z : E => z) 2 (euclideanGaussianLaw E) :=
    (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).mpr
      euclideanGaussian_norm_square_integrable
  have hr : MemLp (fun z : E => ⟪z, u⟫_ℝ) 2 (euclideanGaussianLaw E) := by
    simpa only [real_inner_comm u] using hraw.const_inner u
  have hg : Integrable g (euclideanGaussianLaw E) :=
    (hr.sub (memLp_const b)).integrable_sq.indicator hA
  have hh : Integrable h (euclideanGaussianLaw E) := (integrable_const (1 : ℝ)).indicator hA
  have hgs : StronglyMeasurable g :=
    (((continuous_id.inner continuous_const).sub continuous_const).pow 2).stronglyMeasurable.indicator hA
  have hhs : StronglyMeasurable h := stronglyMeasurable_const.indicator hA
  have hgi : Integrable (fun p => g (F p)) Q :=
    (integrable_map_measure hgs.aestronglyMeasurable hF.aemeasurable).mp (hQ.symm ▸ hg)
  have hhi : Integrable (fun p => h (F p)) Q :=
    (integrable_map_measure hhs.aestronglyMeasurable hF.aemeasurable).mp (hQ.symm ▸ hh)
  have hout : (∫ p, g (F p) ∂Q) ≤ ∫ p, h (F p) ∂Q := by
    rw [integral_prod _ hgi, integral_prod _ hhi]
    apply integral_mono_ae hgi.integral_prod_left hhi.integral_prod_left
    filter_upwards [gaussianOrthogonalResidualLaw_supported (ℝ ∙ u)] with z hz
    let D : Set ℝ := {x : ℝ | x ^ 2 + ‖z‖ ^ 2 ≤ R ^ 2 ∧ x ≤ b}
    have hD : MeasurableSet D := by
      exact (measurableSet_le ((continuous_id.pow 2).add continuous_const).measurable
        measurable_const).inter measurableSet_Iic
    have hi : ⟪z, u⟫_ℝ = 0 := by
      rw [real_inner_comm]
      exact (Submodule.mem_orthogonal _ _).mp hz u (Submodule.mem_span_singleton_self u)
    have he (x : ℝ) : F (z, x) ∈ A ↔ x ∈ D := gaussian_axis_cap_geometry hu hz x R b
    have hg' : (fun x : ℝ => g (F (z, x))) = D.indicator (fun x => (x - b) ^ 2) := by
      funext x
      dsimp only [g]
      by_cases hx : x ∈ D
      · rw [indicator_of_mem ((he x).mpr hx), indicator_of_mem hx]
        dsimp only [F]
        rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hu, hi]
        ring
      · rw [indicator_of_notMem (fun ha => hx ((he x).mp ha)), indicator_of_notMem hx]
    have hh' : (fun x : ℝ => h (F (z, x))) = D.indicator (fun _ => 1) := by
      funext x
      dsimp only [h]
      by_cases hx : x ∈ D
      · rw [indicator_of_mem ((he x).mpr hx), indicator_of_mem hx]
      · rw [indicator_of_notMem (fun ha => hx ((he x).mp ha)), indicator_of_notMem hx]
    rw [hg', hh', integral_indicator hD, integral_indicator hD, integral_const]
    simp only [measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_one]
    exact standardGaussian_negative_quadratic_slice (‖z‖ ^ 2) R hb
  have hgm := integral_map_of_stronglyMeasurable (μ := Q) hF hgs
  have hhm := integral_map_of_stronglyMeasurable (μ := Q) hF hhs
  rw [hQ] at hgm hhm
  rw [← hgm, ← hhm] at hout
  dsimp only [g, h] at hout
  rw [integral_indicator hA, integral_indicator hA, integral_const] at hout
  simpa only [measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_one] using hout

end
end Nonsmooth
