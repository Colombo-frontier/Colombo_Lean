import Nonsmooth.GaussianHalfspaceMean
import Nonsmooth.FiniteObservationIntegral

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianSelection_rank_supported {u : E} (hu : u ≠ 0) {n : ℕ} (w : Fin (n + 1)) :
    ∀ᵐ y ∂supportSelectionValueLaw (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E) u w,
      cdf ((gaussianAmbientRowLaw E).map (fun z : E => ⟪z, u⟫_ℝ)) y ∈ Ioo (0 : ℝ) 1 := by
  have h := rankPower_supported n
  unfold rankPowerLaw at h
  rw [← gaussianSelection_value_rank_law hu w] at h
  exact ae_of_ae_map (continuous_cdf_of_atomless _ (gaussianProjectionLaw_atomless hu)).measurable.aemeasurable h

theorem gaussianSelection_rank_integrable_iff {u : E} (hu : u ≠ 0) {n : ℕ} (w : Fin (n + 1))
    (f : ℝ → ℝ) (hf : StronglyMeasurable f) :
    Integrable (fun y => f (cdf ((gaussianAmbientRowLaw E).map (fun z : E => ⟪z, u⟫_ℝ)) y))
      (supportSelectionValueLaw (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E) u w) ↔
        Integrable f (rankPowerLaw n) := by
  have hc := (continuous_cdf_of_atomless _ (gaussianProjectionLaw_atomless hu)).measurable
  have h := integrable_map_measure (μ := supportSelectionValueLaw
    (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E) u w) hf.aestronglyMeasurable hc.aemeasurable
  rw [gaussianSelection_value_rank_law hu] at h
  exact h.symm

theorem gaussianHalfspaceMean_selected_energy {u : E} (hu : u ≠ 0) (m : ℕ) (w : Fin (m + 3)) :
    (∫ y, ‖gaussianHalfspaceMean u y‖ ^ 2
      ∂supportSelectionValueLaw (fun _ : Fin (m + 3) => gaussianAmbientRowLaw E) u w) ≤
        (2 / (Module.finrank ℝ E : ℝ)) *
          ((2 * Real.log ((m : ℝ) + 3) + 1) / (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3))) := by
  let g : ℝ → ℝ := fun p => ((1 - p) / p) ^ 2 * Real.log (1 / (1 - p))
  have hg : StronglyMeasurable g := (by fun_prop : Measurable g).stronglyMeasurable
  have hK : (0 : ℝ) < (m : ℝ) + 3 := by positivity
  have hent := rankPower_tail_entropy m hK
  have hi := (gaussianSelection_rank_integrable_iff hu (n := m + 2) w g hg).mpr hent.1
  have he : (∫ y, g (cdf ((gaussianAmbientRowLaw E).map (fun z : E => ⟪z, u⟫_ℝ)) y)
      ∂supportSelectionValueLaw (fun _ : Fin (m + 3) => gaussianAmbientRowLaw E) u w) =
        ∫ p, g p ∂rankPowerLaw (m + 2) := by
    rw [← integral_map_of_stronglyMeasurable
      (continuous_cdf_of_atomless _ (gaussianProjectionLaw_atomless hu)).measurable hg,
      gaussianSelection_value_rank_law hu]
    rfl
  have hle := integral_mono_of_nonneg (Eventually.of_forall (fun y => sq_nonneg ‖gaussianHalfspaceMean u y‖))
    (hi.const_mul (2 / (Module.finrank ℝ E : ℝ)))
    (show (fun y => ‖gaussianHalfspaceMean u y‖ ^ 2) ≤ᵐ[
      supportSelectionValueLaw (fun _ : Fin (m + 3) => gaussianAmbientRowLaw E) u w]
      (fun y => (2 / (Module.finrank ℝ E : ℝ)) *
        g (cdf ((gaussianAmbientRowLaw E).map (fun z : E => ⟪z, u⟫_ℝ)) y)) from by
      filter_upwards [gaussianSelection_rank_supported hu (n := m + 2) w] with y hy
      simpa only [g, mul_assoc] using gaussianHalfspaceMean_entropy_bound u y hy)
  rw [integral_const_mul, he] at hle
  apply (hle.trans (mul_le_mul_of_nonneg_left hent.2 (by positivity))).trans_eq
  congr 1
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have hm2 : (m : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hm1, hm2, hK.ne']
  <;> ring

/-- The loser halfspace mean evaluated at the actual maximum response has the stated
integrated bound. Multiplication by the square of the number of losers is left explicit. -/
theorem gaussianHalfspaceMean_maximum_energy {u : E} (hu : u ≠ 0) (m : ℕ) :
    (∫ a : Fin (m + 3) → E, ‖gaussianHalfspaceMean u (finiteSupport a u)‖ ^ 2
      ∂Measure.pi (fun _ : Fin (m + 3) => gaussianAmbientRowLaw E)) ≤
        (2 / (Module.finrank ℝ E : ℝ)) *
          ((2 * Real.log ((m : ℝ) + 3) + 1) / (((m : ℝ) + 1) * ((m : ℝ) + 2))) := by
  let Q := Measure.pi (fun _ : Fin (m + 3) => gaussianAmbientRowLaw E)
  let ν := Q.map (supportSingleObservation u)
  have hO := supportSingleObservation_measurable (E := E) (k := m + 3) u
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hO.aemeasurable
  have hL : StronglyMeasurable (fun h : Fin (m + 3) × ℝ => gaussianHalfspaceMean u h.2) :=
    (gaussianHalfspaceMean_stronglyMeasurable u).comp_measurable measurable_snd
  have hLp : MemLp (fun h : Fin (m + 3) × ℝ => gaussianHalfspaceMean u h.2) 2 ν :=
    MemLp.of_bound hL.aestronglyMeasurable 2
      (Eventually.of_forall (fun h => gaussianHalfspaceMean_norm_le u h.2))
  have hfi := (memLp_two_iff_integrable_sq_norm hLp.aestronglyMeasurable).mp hLp
  have hfm : StronglyMeasurable (fun h : Fin (m + 3) × ℝ => ‖gaussianHalfspaceMean u h.2‖ ^ 2) := hL.norm.pow 2
  have he := finite_first_integral ν _ hfm hfi
  have hmap := integral_map_of_stronglyMeasurable (μ := Q) hO hfm
  dsimp only [supportSingleObservation] at hmap
  change (∫ a : Fin (m + 3) → E, ‖gaussianHalfspaceMean u (finiteSupport a u)‖ ^ 2 ∂Q) ≤ _
  rw [← hmap, he]
  dsimp only [ν, Q]
  simp_rw [← supportSelectionValueLaw_eq]
  calc
    _ ≤ ∑ _w : Fin (m + 3), (2 / (Module.finrank ℝ E : ℝ)) *
        ((2 * Real.log ((m : ℝ) + 3) + 1) / (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3))) :=
      Finset.sum_le_sum (fun w _ => gaussianHalfspaceMean_selected_energy hu m w)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
      have hm2 : (m : ℝ) + 2 ≠ 0 := by positivity
      have hm3 : (m : ℝ) + 3 ≠ 0 := by positivity
      have hd : (Module.finrank ℝ E : ℝ) ≠ 0 := (Nat.cast_pos.mpr Module.finrank_pos).ne'
      field_simp [hm1, hm2, hm3, hd]
      <;> ring

end
end Nonsmooth
