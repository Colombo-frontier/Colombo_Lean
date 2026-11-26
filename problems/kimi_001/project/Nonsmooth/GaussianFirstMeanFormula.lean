import Nonsmooth.GaussianLoserEnergy

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] {n : ℕ}

/-- Exact first-observation aggregate posterior mean under the actual truncated Gaussian prior. -/
theorem gaussianPosterior_first_aggregate_mean {u : E} (hu : ‖u‖ = 1) :
    ∀ᵐ h ∂(Measure.pi (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E)).map (supportSingleObservation u),
      (∫ a : Fin (n + 1) → E, ∑ i, a i
        ∂condDistrib id (supportSingleObservation u)
          (Measure.pi (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E)) h) =
        h.2 • u + (n : ℝ) • gaussianHalfspaceMean u h.2 := by
  let Q := Measure.pi (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E)
  have hune : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; norm_num)
  have hci : ∀ᵐ h ∂Q.map (supportSingleObservation u),
      ∀ i : Fin (n + 1), Integrable (fun a : Fin (n + 1) → E => a i)
        (condDistrib id (supportSingleObservation u) Q h) := by
    apply ae_all_iff.mpr
    intro i
    have hi := (gaussianAmbientRows_coordinate_memLp (E := E) i).integrable (by norm_num)
    exact (hi.comp_snd_map_prodMk (supportSingleObservation u)).condDistrib_ae_map (Y := id) aemeasurable_id
  filter_upwards [supportSelectionKernel_ae_eq_condDistrib
    (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E) u, gaussianPosterior_winner_mean (n := n) hu, hci]
    with h hk hw hi
  have hl (i : Fin (n + 1)) (hni : i ≠ h.1) :
      (∫ a : Fin (n + 1) → E, a i ∂condDistrib id (supportSingleObservation u) Q h) =
        gaussianHalfspaceMean u h.2 := by
    rw [← hk]
    have he := integral_map_of_stronglyMeasurable
      (μ := supportSelectionKernel (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E) u h)
      (measurable_pi_apply i) (stronglyMeasurable_id : StronglyMeasurable (fun z : E => z))
    rw [supportSelectionKernel_coordinate, gaussianSelection_loser_kernel hune h.1 i hni h.2] at he
    exact he.symm
  rw [integral_finsetSum _ (fun i _ => hi i), Fin.sum_univ_succAbove _ h.1, hw]
  have hls (j : Fin n) :
      (∫ a : Fin (n + 1) → E, a (h.1.succAbove j) ∂condDistrib id (supportSingleObservation u) Q h) =
        gaussianHalfspaceMean u h.2 := hl _ (h.1.succAbove_ne j)
  simp only [hls, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul]

theorem gaussian_first_condExp_formula {u : E} (hu : ‖u‖ = 1) :
    ((Measure.pi (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E))[
      fun a => ∑ i, a i | MeasurableSpace.comap (supportSingleObservation u) inferInstance]) =ᵐ[
        Measure.pi (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E)]
      (fun a => (finiteSupport a u) • u + (n : ℝ) • gaussianHalfspaceMean u (finiteSupport a u)) := by
  have hO := supportSingleObservation_measurable (E := E) (k := n + 1) u
  have hpost := ae_of_ae_map hO.aemeasurable (gaussianPosterior_first_aggregate_mean (n := n) hu)
  have hce := condExp_ae_eq_integral_condDistrib_id hO
    (gaussianAmbientRows_aggregate_integrable (E := E) (k := n + 1))
  filter_upwards [hpost, hce] with a ha hc
  exact hc.trans ha

end
end Nonsmooth
