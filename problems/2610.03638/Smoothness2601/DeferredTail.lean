import Bilevel.ProjectionConcentration

/-! Conditional unseen-column concentration for genuine Haar prefix exposure.
Queries are bounded but arbitrary: they do not expose their scalar projections.
The exponent uses the already verified weaker spherical constant 1/8. -/
noncomputable section
namespace Smoothness2601.DeferredPrefix
open MeasureTheory ProbabilityTheory
open Bilevel EuclideanGaussian ProjectionPosterior ProjectionGeometry
open scoped RealInnerProductSpace BigOperators ENNReal
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000

def UnseenOrthogonal (d T k : ℕ) (V : Submodule ℝ (Space d)) (U : Frame d T) : Prop :=
  ∀ i : Fin T, k ≤ i.val → U i ∈ Vᗮ

theorem unseen_measurable (d T k : ℕ) (V : Submodule ℝ (Space d)) :
    MeasurableSet {U : Frame d T | UnseenOrthogonal d T k V U} := by
  unfold UnseenOrthogonal
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _
  exact V.isClosed_orthogonal.measurableSet.preimage (measurable_pi_apply i)

theorem unseen_after_reveal (d T k : ℕ) (V : Submodule ℝ (Space d))
    (μ : Measure (Frame d T)) [IsProbabilityMeasure μ]
    (hU : ∀ᵐ U ∂μ, Orthonormal ℝ U)
    (horth : ∀ᵐ U ∂μ, UnseenOrthogonal d T k V U) (i : Fin T) (hi : i.val = k) :
    ∀ᵐ y ∂μ.map (revealObservation d T i),
      ∀ᵐ U ∂condDistrib id (revealObservation d T i) μ y,
        UnseenOrthogonal d T (k+1) (V ⊔ Submodule.span ℝ {y}) U := by
  have ho := ConditionalSupport.support μ (revealObservation d T i) (reveal_measurable d T i)
    {U | UnseenOrthogonal d T k V U} (unseen_measurable d T k V) horth
  filter_upwards [ho,ProjectionConcentration.conditioned_orthonormal d T μ hU
    (revealObservation d T i) (reveal_measurable d T i),reveal_fiber d T μ i] with y hy hyU hyi
  filter_upwards [hy,hyU,hyi] with U hUV hUU hUi
  intro j hj
  rw [← Submodule.inf_orthogonal,Submodule.mem_inf]
  refine ⟨hUV j (by omega),?_⟩
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right,← hUi]
  exact hUU.inner_eq_zero (by intro hij; have := congrArg Fin.val hij; omega)

theorem residual_inner_unseen (d : ℕ) (V : Submodule ℝ (Space d)) (w u : Space d)
    (hu : u ∈ Vᗮ) : ⟪residual V w,u⟫ = ⟪w,u⟫ := by
  rw [ProjectionGeometry.residual,inner_sub_left,
    Submodule.inner_right_of_mem_orthogonal (project_mem V w) hu,sub_zero]

theorem bounded_query_tail (d T k n : ℕ) (V : Submodule ℝ (Space d))
    (hn : n+1 ≤ Module.finrank ℝ Vᗮ) {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hδR : δ ≤ R)
    (μ : Measure (Frame d T)) [IsProbabilityMeasure μ] (hμ : Invariant d T V μ)
    (hU : ∀ᵐ U ∂μ, Orthonormal ℝ U) (horth : ∀ᵐ U ∂μ, UnseenOrthogonal d T k V U)
    (w : Space d) (hw : ‖w‖ ≤ R) :
    μ {U | ∃ i : Fin T, k ≤ i.val ∧ δ ≤ |⟪w,U i⟫|} ≤
      ENNReal.ofReal ((T : ℝ)*(2*Real.exp (-(n : ℝ)*(δ^2/R^2)/8))) := by
  let v := residual V w
  have hvV : v ∈ Vᗮ := Submodule.sub_orthogonalProjection_mem_orthogonal w
  have hvR : ‖v‖ ≤ R := (ProjectionQuery.residual_norm_le V w).trans hw
  by_cases hv : v = 0
  · have he : ∀ᵐ U ∂μ, U ∉ {U | ∃ i : Fin T, k ≤ i.val ∧ δ ≤ |⟪w,U i⟫|} := by
      filter_upwards [horth] with U hUO
      rintro ⟨i,hik,hiδ⟩
      have he := residual_inner_unseen d V w (U i) (hUO i hik)
      change ⟪v,U i⟫ = _ at he
      rw [hv,inner_zero_left] at he
      rw [← he,abs_zero] at hiδ
      linarith
    have he0 : μ {U | ∃ i : Fin T, k ≤ i.val ∧ δ ≤ |⟪w,U i⟫|} = 0 := by
      simpa only [ae_iff,not_not] using he
    rw [he0]
    exact zero_le _
  · let q := ‖v‖⁻¹ • v
    have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hqV : q ∈ Vᗮ := Vᗮ.smul_mem _ hvV
    have hqn : ‖q‖ = 1 := by simp [q,norm_smul,Real.norm_eq_abs,abs_of_pos hvp,hvp.ne']
    have htpos : 0 < δ^2/R^2 := div_pos (sq_pos_of_pos hδ) (sq_pos_of_pos hR)
    have ht2 : δ^2/R^2 ≤ 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
      nlinarith
    have ht := ProjectionConcentration.query_tail_dimension d T V n hn (δ^2/R^2) htpos ht2 μ hμ q hqV hqn hU
    have hincl : ∀ᵐ U ∂μ,
        U ∈ {U | ∃ i : Fin T, k ≤ i.val ∧ δ ≤ |⟪w,U i⟫|} →
        U ∈ {U | ∃ i : Fin T, δ^2/R^2 ≤ ⟪q,U i⟫^2} := by
      filter_upwards [horth] with U hUO
      rintro ⟨i,hik,hiδ⟩
      refine ⟨i,?_⟩
      have he : ⟪w,U i⟫ = ‖v‖*⟪q,U i⟫ := by
        rw [← residual_inner_unseen d V w (U i) (hUO i hik)]
        dsimp only [q]
        rw [real_inner_smul_left]
        field_simp
        rfl
      have hsq : δ^2 ≤ ‖v‖^2*⟪q,U i⟫^2 := by
        have hh := (sq_le_sq₀ hδ.le (abs_nonneg _)).mpr hiδ
        rw [sq_abs,he,mul_pow] at hh
        exact hh
      apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
      have hnorm : ‖v‖^2 ≤ R^2 := (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hvR
      nlinarith [mul_le_mul_of_nonneg_right hnorm (sq_nonneg ⟪q,U i⟫)]
    apply (measure_mono_ae hincl).trans
    simpa only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] using ENNReal.ofReal_le_ofReal ht

end Smoothness2601.DeferredPrefix
