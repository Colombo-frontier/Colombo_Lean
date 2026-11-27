import Nonsmooth.ConeCapGeometry

open MeasureTheory MeasureTheory.Measure Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem addHaar_cap_volume_lower (μ : Measure E) [IsAddHaarMeasure μ]
    {G : Set E} (hG : Convex ℝ G) {r t : ℝ} {e : E}
    (he : ‖e‖ = 1) (hre : r • e ∈ G) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ENNReal.ofReal (t ^ Module.finrank ℝ E) * μ {y | y ∈ G ∧ 0 ≤ ⟪y, e⟫_ℝ} ≤
      μ {z | z ∈ G ∧ (1 - t) * r ≤ ⟪z, e⟫_ℝ} := by
  have hm := measure_mono (μ := μ) (convex_halfspace_contraction_subset_cap hG he hre ht ht1)
  rwa [addHaar_convex_contraction μ _ (r • e) ht] at hm

theorem addHaar_fixed_cap_volume_lower (μ : Measure E) [IsAddHaarMeasure μ]
    {G : Set E} (hG : Convex ℝ G) {r : ℝ} {e : E}
    (he : ‖e‖ = 1) (hre : r • e ∈ G) (hd : 0 < Module.finrank ℝ E) :
    ENNReal.ofReal (1 / 2 : ℝ) * μ {y | y ∈ G ∧ 0 ≤ ⟪y, e⟫_ℝ} ≤
      μ {z | z ∈ G ∧ r / (2 * (Module.finrank ℝ E : ℝ)) ≤ ⟪z, e⟫_ℝ} := by
  have ht := fixed_cap_contraction_bounds (Module.finrank ℝ E) hd
  have hm := addHaar_cap_volume_lower μ hG he hre ht.1 ht.2
  have hp := ENNReal.ofReal_le_ofReal (fixed_cap_contraction_volume_factor (Module.finrank ℝ E) hd)
  have hp' := mul_le_mul_right' hp (μ {y | y ∈ G ∧ 0 ≤ ⟪y, e⟫_ℝ})
  have heq : (1 - (1 - 1 / (2 * (Module.finrank ℝ E : ℝ)))) * r =
      r / (2 * (Module.finrank ℝ E : ℝ)) := by ring
  rw [heq] at hm
  exact hp'.trans hm

theorem addHaar_cap_fraction_of_halfspace_fraction (μ : Measure E) [IsAddHaarMeasure μ]
    {G : Set E} (hG : Convex ℝ G) {r : ℝ} {e : E} {κ : ℝ≥0∞}
    (he : ‖e‖ = 1) (hre : r • e ∈ G) (hd : 0 < Module.finrank ℝ E)
    (hhalf : κ * μ G ≤ μ {y | y ∈ G ∧ 0 ≤ ⟪y, e⟫_ℝ}) :
    (ENNReal.ofReal (1 / 2 : ℝ) * κ) * μ G ≤
      μ {z | z ∈ G ∧ r / (2 * (Module.finrank ℝ E : ℝ)) ≤ ⟪z, e⟫_ℝ} := by
  rw [mul_assoc]
  exact (mul_le_mul_left' hhalf _).trans (addHaar_fixed_cap_volume_lower μ hG he hre hd)

omit [FiniteDimensional ℝ E] in
theorem separated_cap_retained_volume_add_le (μ : Measure E) {G : Set E} (hG : MeasurableSet G)
    (e : E) {τ σ : ℝ} (hτσ : τ < σ) :
    μ {z | z ∈ G ∧ ⟪z, e⟫_ℝ ≤ τ} + μ {z | z ∈ G ∧ σ ≤ ⟪z, e⟫_ℝ} ≤ μ G := by
  have hm : Measurable (fun z : E => ⟪z, e⟫_ℝ) := (continuous_id.inner continuous_const).measurable
  have hcap : MeasurableSet {z | z ∈ G ∧ σ ≤ ⟪z, e⟫_ℝ} := hG.inter (measurableSet_le measurable_const hm)
  have hd : Disjoint {z | z ∈ G ∧ ⟪z, e⟫_ℝ ≤ τ} {z | z ∈ G ∧ σ ≤ ⟪z, e⟫_ℝ} := by
    apply Set.disjoint_left.mpr
    intro z hz1 hz2
    exact (not_le_of_gt hτσ) (hz2.2.trans hz1.2)
  rw [← measure_union hd hcap]
  exact measure_mono (by intro z hz; rcases hz with hz | hz <;> exact hz.1)

end
end Nonsmooth
