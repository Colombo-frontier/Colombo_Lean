import Nonsmooth.GaussianMaximumMoment

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

theorem finite_first_ae {β : Type} [MeasurableSpace β] {k : ℕ}
    (ν : Measure (Fin k × β)) (P : Fin k × β → Prop)
    (hP : ∀ w : Fin k, ∀ᵐ y ∂((ν.restrict (Prod.fst ⁻¹' {w})).map Prod.snd), P (w, y)) :
    ∀ᵐ h ∂ν, P h := by
  have hw (w : Fin k) : ∀ᵐ h ∂ν, h.1 = w → P (w, h.2) := by
    have he := ae_of_ae_map measurable_snd.aemeasurable (hP w)
    exact (ae_restrict_iff' (measurable_fst (measurableSet_singleton w))).mp he
  filter_upwards [ae_all_iff.mpr hw] with h hh
  exact hh h.1 rfl

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] {n : ℕ}

theorem gaussianSelection_winner_mean {u : E} (hu : ‖u‖ = 1) :
    ∀ᵐ h ∂(Measure.pi (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E)).map (supportSingleObservation u),
      (∫ z, z ∂supportSelectionRowKernel (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E) u h.1 h) =
        h.2 • u := by
  apply finite_first_ae
  intro w
  rw [← supportSelectionValueLaw_eq]
  have habs : supportSelectionValueLaw (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E) u w ≪
      (gaussianAmbientRowLaw E).map (fun z : E => ⟪z, u⟫_ℝ) :=
    withDensity_absolutelyContinuous _ _
  filter_upwards [habs.ae_le (gaussianAmbientRowLaw_projection_slice_mean hu)] with y hy
  rw [supportSelectionRowKernel_winner]
  exact hy

/-- The actual posterior winning-row barycenter equals the observed maximum times the unit
query, including the deterministic least-index tie rule. -/
theorem gaussianPosterior_winner_mean {u : E} (hu : ‖u‖ = 1) :
    ∀ᵐ h ∂(Measure.pi (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E)).map (supportSingleObservation u),
      (∫ a : Fin (n + 1) → E, a h.1
        ∂condDistrib id (supportSingleObservation u)
          (Measure.pi (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E)) h) = h.2 • u := by
  filter_upwards [supportSelectionKernel_ae_eq_condDistrib
    (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E) u, gaussianSelection_winner_mean (n := n) hu]
    with h hk hm
  rw [← hk]
  have he := integral_map_of_stronglyMeasurable
    (μ := supportSelectionKernel (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E) u h)
    (measurable_pi_apply h.1) (stronglyMeasurable_id : StronglyMeasurable (fun z : E => z))
  rw [supportSelectionKernel_coordinate] at he
  exact he.symm.trans hm

theorem gaussianPosterior_winner_mean_energy {u : E} (hu : ‖u‖ = 1) :
    (∫ h : Fin (n + 1) × ℝ,
      ‖∫ a : Fin (n + 1) → E, a h.1
        ∂condDistrib id (supportSingleObservation u)
          (Measure.pi (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E)) h‖ ^ 2
      ∂(Measure.pi (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E)).map (supportSingleObservation u)) ≤
        4 * Real.log (2 * (n + 1 : ℕ)) / (Module.finrank ℝ E : ℝ) := by
  calc
    _ = ∫ h : Fin (n + 1) × ℝ, h.2 ^ 2
        ∂(Measure.pi (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E)).map (supportSingleObservation u) := by
      apply integral_congr_ae
      filter_upwards [gaussianPosterior_winner_mean (n := n) hu] with h hh
      rw [hh, norm_smul, hu]
      simp
    _ = ∫ a : Fin (n + 1) → E, (finiteSupport a u) ^ 2
        ∂Measure.pi (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E) :=
      integral_map_of_stronglyMeasurable (supportSingleObservation_measurable u)
        (continuous_snd.pow 2).stronglyMeasurable
    _ ≤ _ := gaussianAmbientRows_support_second_log hu

end
end Nonsmooth
