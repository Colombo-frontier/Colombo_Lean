import Nonsmooth.GaussianSlabCovariance

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {n : ℕ}

theorem supportSelection_winner_property
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E)
    (P : Fin (n + 1) → Measure E → Prop)
    (hP : ∀ i, ∀ᵐ y ∂(μ i).map (fun z : E => ⟪z, u⟫_ℝ),
      P i (condDistrib id (fun z : E => ⟪z, u⟫_ℝ) (μ i) y)) :
    ∀ᵐ h ∂(Measure.pi μ).map (supportSingleObservation u),
      P h.1 (supportSelectionRowKernel μ u h.1 h) := by
  apply finite_first_ae
  intro w
  rw [← supportSelectionValueLaw_eq]
  have hac : supportSelectionValueLaw μ u w ≪ (μ w).map (fun z : E => ⟪z, u⟫_ℝ) :=
    withDensity_absolutelyContinuous _ _
  filter_upwards [hac.ae_le (hP w)] with y hy
  rw [supportSelectionRowKernel_winner]
  exact hy

/-- Row properties survive maximum-and-index selection when they hold for
projection slices, nonwinner restrictions, and the zero-mass fallback. -/
theorem supportSelection_row_property
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E)
    (P : Fin (n + 1) → Measure E → Prop) (hbase : ∀ i, P i (μ i))
    (hwinner : ∀ i, ∀ᵐ y ∂(μ i).map (fun z : E => ⟪z, u⟫_ℝ),
      P i (condDistrib id (fun z : E => ⟪z, u⟫_ℝ) (μ i) y))
    (hloser : ∀ (w i : Fin (n + 1)) (y : ℝ), i ≠ w →
      μ i (Prod.mk (w, y) ⁻¹' supportLoserRegion u i) ≠ 0 →
        P i ((μ i)[|Prod.mk (w, y) ⁻¹' supportLoserRegion u i])) :
    ∀ᵐ h ∂(Measure.pi μ).map (supportSingleObservation u),
      ∀ i, P i (supportSelectionRowKernel μ u i h) := by
  classical
  filter_upwards [supportSelection_winner_property μ u P hwinner] with h hh
  intro i
  by_cases hi : i = h.1
  · rw [hi]
    exact hh
  · obtain ⟨w, y⟩ := h
    by_cases hpos : μ i (Prod.mk (w, y) ⁻¹' supportLoserRegion u i) = 0
    · have he : supportSelectionRowKernel μ u i (w, y) = μ i := by
        rw [supportSelectionRowKernel, Kernel.piecewise_apply]
        simp only [mem_preimage, mem_singleton_iff, Ne.symm hi, if_false]
        change (if μ i (Prod.mk (w, y) ⁻¹' supportLoserRegion u i) = 0 then _ else _) = _
        rw [if_pos hpos]
      rw [he]
      exact hbase i
    · rw [supportSelectionRowKernel_loser μ u w i hi y hpos]
      exact hloser w i y hi hpos

theorem supportPosterior_covariance_of_selection_rows
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E)
    (B : Fin (n + 1) → E → ℝ)
    (hc : ∀ᵐ h ∂(Measure.pi μ).map (supportSingleObservation u), ∀ (v : E) (i : Fin (n + 1)),
      variance (fun z : E => ⟪v, z⟫_ℝ) (supportSelectionRowKernel μ u i h) ≤ B i v) :
    ∀ᵐ h ∂(Measure.pi μ).map (supportSingleObservation u), ∀ (v : E) (i : Fin (n + 1)),
      variance (fun a : Fin (n + 1) → E => ⟪v, a i⟫_ℝ)
        (condDistrib id (supportSingleObservation u) (Measure.pi μ) h) ≤ B i v := by
  filter_upwards [supportSelectionKernel_ae_eq_condDistrib μ u, hc] with h hk hc
  intro v i
  rw [← hk]
  have hi : Measurable (fun z : E => ⟪v, z⟫_ℝ) := (continuous_const.inner continuous_id).measurable
  have he := variance_map_measurable (supportSelectionKernel μ u h)
    (fun a : Fin (n + 1) → E => a i) (measurable_pi_apply i) (fun z : E => ⟪v, z⟫_ℝ) hi
  rw [supportSelectionKernel_coordinate] at he
  exact he.symm.trans_le (hc v i)

end
end Nonsmooth
