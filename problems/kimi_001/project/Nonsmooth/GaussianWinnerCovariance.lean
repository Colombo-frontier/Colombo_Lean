import Nonsmooth.GaussianScaledSlices
import Nonsmooth.SelectionPosterior

open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] {n : ℕ}

theorem gaussianSelection_winner_covariance {u : E} (hu : ‖u‖ = 1) :
    ∀ᵐ h ∂(Measure.pi (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E)).map (supportSingleObservation u),
      ∀ v : E, variance (fun z : E => ⟪v, z⟫_ℝ)
        (supportSelectionRowKernel (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E) u h.1 h) ≤
          ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  have hfirst (ν : Measure (Fin (n + 1) × ℝ)) (P : Fin (n + 1) × ℝ → Prop)
      (hP : ∀ w : Fin (n + 1), ∀ᵐ y ∂((ν.restrict (Prod.fst ⁻¹' {w})).map Prod.snd), P (w, y)) :
      ∀ᵐ h ∂ν, P h := by
    have hw (w : Fin (n + 1)) : ∀ᵐ h ∂ν, h.1 = w → P (w, h.2) := by
      have he := ae_of_ae_map measurable_snd.aemeasurable (hP w)
      exact (ae_restrict_iff' (measurable_fst (measurableSet_singleton w))).mp he
    filter_upwards [ae_all_iff.mpr hw] with h hh
    exact hh h.1 rfl
  apply hfirst
  intro w
  rw [← supportSelectionValueLaw_eq]
  have habs : supportSelectionValueLaw (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E) u w ≪
      (gaussianAmbientRowLaw E).map (fun z : E => ⟪z, u⟫_ℝ) :=
    withDensity_absolutelyContinuous _ _
  filter_upwards [habs.ae_le (gaussianAmbientRow_scalar_covariance hu)] with y hy
  rw [supportSelectionRowKernel_winner]
  exact hy

/-- The winning row after the first maximum-and-index observation satisfies the
sharp conditional covariance bound for the actual scaled truncated Gaussian prior. -/
theorem gaussianPosterior_winner_covariance {u : E} (hu : ‖u‖ = 1) :
    ∀ᵐ h ∂(Measure.pi (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E)).map (supportSingleObservation u),
      ∀ v : E, variance (fun a : Fin (n + 1) → E => ⟪v, a h.1⟫_ℝ)
        (condDistrib id (supportSingleObservation u)
          (Measure.pi (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E)) h) ≤
            ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  filter_upwards [supportSelectionKernel_ae_eq_condDistrib
    (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E) u,
    gaussianSelection_winner_covariance (n := n) hu] with h hk hc
  intro v
  rw [← hk]
  have hi : Measurable (fun z : E => ⟪v, z⟫_ℝ) :=
    (continuous_const.inner continuous_id).measurable
  have he := variance_map_measurable
    (supportSelectionKernel (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E) u h)
    (fun a : Fin (n + 1) → E => a h.1) (measurable_pi_apply h.1) (fun z : E => ⟪v, z⟫_ℝ) hi
  rw [supportSelectionKernel_coordinate] at he
  exact he.symm.trans_le (hc v)

end
end Nonsmooth
