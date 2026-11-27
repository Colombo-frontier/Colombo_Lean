import Nonsmooth.GaussianSlabSelection

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem kernel_variance_measurable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) [IsSFiniteKernel κ] (f : β → ℝ) (hf : Measurable f) :
    Measurable (fun x => variance f (κ x)) := by
  have hm : Measurable (fun x => ∫ z, f z ∂κ x) := hf.stronglyMeasurable.integral_kernel.measurable
  have hg : Measurable (fun p : α × β => (f p.2 - ∫ z, f z ∂κ p.1) ^ 2) :=
    ((hf.comp measurable_snd).sub (hm.comp measurable_fst)).pow_const 2
  simp_rw [variance_eq_integral hf.aemeasurable]
  exact hg.stronglyMeasurable.integral_kernel_prod_right'.measurable

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem directional_variance_continuous (μ : Measure E) [IsProbabilityMeasure μ]
    (hV : MemLp (fun z : E => z) 2 μ) :
    Continuous (fun v : E => variance (fun z : E => ⟪v, z⟫_ℝ) μ) := by
  let m : E := ∫ z : E, z ∂μ
  have hc : MemLp (fun z : E => z - m) 2 μ := hV.sub (memLp_const m)
  have he (v : E) : variance (fun z : E => ⟪v, z⟫_ℝ) μ = ∫ z : E, ⟪v, z - m⟫_ℝ ^ 2 ∂μ := by
    have hv : Measurable (fun z : E => ⟪v, z⟫_ℝ) := (continuous_const.inner continuous_id).measurable
    rw [variance_eq_integral hv.aemeasurable,
      integral_inner (hV.integrable (by norm_num))]
    simp only [inner_sub_right, m]
  simp_rw [he]
  apply continuous_iff_continuousAt.mpr
  intro v₀
  apply continuousAt_of_dominated (bound := fun z : E => (‖v₀‖ + 1) ^ 2 * ‖z - m‖ ^ 2)
  · exact Eventually.of_forall (fun v => ((hc.const_inner v).aestronglyMeasurable.pow 2))
  · filter_upwards [Metric.ball_mem_nhds v₀ (by norm_num : (0 : ℝ) < 1)] with v hv
    have hv' : ‖v - v₀‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hv
    have hn : ‖v‖ ≤ ‖v₀‖ + 1 := by
      have h := norm_add_le (v - v₀) v₀
      rw [sub_add_cancel] at h
      linarith
    apply Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hi : |⟪v, z - m⟫_ℝ| ≤ (‖v₀‖ + 1) * ‖z - m‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    nlinarith [abs_nonneg ⟪v, z - m⟫_ℝ, sq_abs ⟪v, z - m⟫_ℝ]
  · exact hc.norm.integrable_sq.const_mul _
  · exact Eventually.of_forall (fun z => ((continuous_id.inner continuous_const).pow 2).continuousAt)

theorem kernel_covariance_bound_measurable {α : Type} [MeasurableSpace α]
    (κ : Kernel α E) [IsMarkovKernel κ] (hV : ∀ x, MemLp (fun z : E => z) 2 (κ x))
    (c : ℝ) : MeasurableSet {x : α | ∀ v : E, variance (fun z : E => ⟪v, z⟫_ℝ) (κ x) ≤ c * ‖v‖ ^ 2} := by
  obtain ⟨D, hD, hdense⟩ := TopologicalSpace.exists_countable_dense E
  have he : {x : α | ∀ v : E, variance (fun z : E => ⟪v, z⟫_ℝ) (κ x) ≤ c * ‖v‖ ^ 2} =
      ⋂ v ∈ D, {x : α | variance (fun z : E => ⟪v, z⟫_ℝ) (κ x) ≤ c * ‖v‖ ^ 2} := by
    ext x
    simp only [mem_setOf_eq, mem_iInter]
    constructor
    · exact fun h v _ => h v
    · intro h
      have hs : IsClosed {v : E | variance (fun z : E => ⟪v, z⟫_ℝ) (κ x) ≤ c * ‖v‖ ^ 2} :=
        isClosed_le (directional_variance_continuous (κ x) (hV x))
          (continuous_const.mul (continuous_norm.pow 2))
      have hsub := closure_minimal h hs
      rw [hdense.closure_eq] at hsub
      exact fun v => hsub (mem_univ v)
  rw [he]
  exact MeasurableSet.biInter hD (fun v _ => measurableSet_le
    (kernel_variance_measurable κ _ (continuous_const.inner continuous_id).measurable) measurable_const)

/-- The exceptional null set can be chosen jointly for all directions when
mixing a parameter-dependent posterior, using a countable dense set and L2 continuity. -/
theorem kernel_covariance_ae_compProd {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) [IsFiniteMeasure ν] (η : Kernel α β) [IsMarkovKernel η]
    (κ : Kernel (α × β) E) [IsMarkovKernel κ] (c : ℝ)
    (hV : ∀ᵐ p ∂ν ⊗ₘ η, MemLp (fun z : E => z) 2 (κ p))
    (hcov : ∀ᵐ x ∂ν, ∀ᵐ y ∂η x, ∀ v : E,
      variance (fun z : E => ⟪v, z⟫_ℝ) (κ (x, y)) ≤ c * ‖v‖ ^ 2) :
    ∀ᵐ p ∂ν ⊗ₘ η, ∀ v : E, variance (fun z : E => ⟪v, z⟫_ℝ) (κ p) ≤ c * ‖v‖ ^ 2 := by
  obtain ⟨D, hD, hdense⟩ := TopologicalSpace.exists_countable_dense E
  have hmeas : MeasurableSet {p : α × β | ∀ v ∈ D,
      variance (fun z : E => ⟪v, z⟫_ℝ) (κ p) ≤ c * ‖v‖ ^ 2} := by
    have he : {p : α × β | ∀ v ∈ D, variance (fun z : E => ⟪v, z⟫_ℝ) (κ p) ≤ c * ‖v‖ ^ 2} =
        ⋂ v ∈ D, {p : α × β | variance (fun z : E => ⟪v, z⟫_ℝ) (κ p) ≤ c * ‖v‖ ^ 2} := by
      ext p
      simp only [mem_setOf_eq, mem_iInter]
    rw [he]
    exact MeasurableSet.biInter hD (fun v _ => measurableSet_le
      (kernel_variance_measurable κ _ (continuous_const.inner continuous_id).measurable) measurable_const)
  have hbound : ∀ᵐ p ∂ν ⊗ₘ η, ∀ v ∈ D,
      variance (fun z : E => ⟪v, z⟫_ℝ) (κ p) ≤ c * ‖v‖ ^ 2 := by
    apply (Measure.ae_compProd_iff hmeas).mpr
    filter_upwards [hcov] with x hx
    exact hx.mono (fun y hy v _ => hy v)
  filter_upwards [hV, hbound] with p hp hb
  have hs : IsClosed {v : E | variance (fun z : E => ⟪v, z⟫_ℝ) (κ p) ≤ c * ‖v‖ ^ 2} :=
    isClosed_le (directional_variance_continuous (κ p) hp) (continuous_const.mul (continuous_norm.pow 2))
  have hsub := closure_minimal hb hs
  rw [hdense.closure_eq] at hsub
  exact fun v => hsub (mem_univ v)

end
end Nonsmooth
