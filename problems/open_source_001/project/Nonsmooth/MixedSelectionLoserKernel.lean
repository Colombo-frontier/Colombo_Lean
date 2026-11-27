import Nonsmooth.SupportLoserShift
import Nonsmooth.ConstantObservationAE

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem supportSelection_loser_halfspace_kernel_mixed {k : ℕ}
    (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E)
    (w i : Fin k) (hni : i ≠ w)
    (hD : (∃ c : ℝ, ∀ᵐ z ∂μ i, ⟪z, u⟫_ℝ = c) ∨
      ∀ y : ℝ, μ i {z : E | ⟪z, u⟫_ℝ = y} = 0) (y : ℝ) :
    supportSelectionRowKernel μ u i (w, y) = halfspacePosteriorKernel (μ i) u y := by
  classical
  rw [supportSelectionRowKernel, Kernel.piecewise_apply]
  simp only [mem_preimage, mem_singleton_iff, Ne.symm hni, if_false]
  change (if μ i (Prod.mk (w, y) ⁻¹' supportLoserRegion u i) = 0
      then μ i else (μ i)[|Prod.mk (w, y) ⁻¹' supportLoserRegion u i]) =
    (if μ i {z : E | ⟪z, u⟫_ℝ ≤ y} = 0
      then μ i else (μ i)[|{z : E | ⟪z, u⟫_ℝ ≤ y}])
  rcases hD with ⟨c, hc⟩ | hzero
  · have hdecision : ∀ᵐ z ∂μ i, (z ∈ Prod.mk (w, y) ⁻¹' supportLoserRegion u i) ↔
        (c ≤ y ∧ (¬ i < w ∨ c < y)) := by
      filter_upwards [hc] with z hz
      change (⟪z, u⟫_ℝ ≤ y ∧ (¬ i < w ∨ ⟪z, u⟫_ℝ < y)) ↔ _
      rw [hz]
    have hleft : (if μ i (Prod.mk (w, y) ⁻¹' supportLoserRegion u i) = 0
        then μ i else (μ i)[|Prod.mk (w, y) ⁻¹' supportLoserRegion u i]) = μ i := by
      split_ifs with hp
      · rfl
      · exact cond_eq_self_of_ae_event_decision (μ i) _
          (measurable_prodMk_left (supportLoserRegion_measurable u i)) _ hdecision hp
    have hright : (if μ i {z : E | ⟪z, u⟫_ℝ ≤ y} = 0
        then μ i else (μ i)[|{z : E | ⟪z, u⟫_ℝ ≤ y}]) = μ i := by
      split_ifs with hp
      · rfl
      · exact constant_real_observation_condition (μ i) _ (by fun_prop) c hc
          (Iic y) measurableSet_Iic hp
    exact hleft.trans hright.symm
  · have he := supportLoserRegion_ae_halfspace (μ i) hzero w i y
    simp only [measure_congr he, ProbabilityTheory.cond, Measure.restrict_congr_set he]

theorem supportPosteriorShift_loser_ae_mixed {n : ℕ}
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E)
    (hD : ∀ i, (∃ c : ℝ, ∀ᵐ z ∂μ i, ⟪z, u⟫_ℝ = c) ∨
      ∀ y : ℝ, μ i {z : E | ⟪z, u⟫_ℝ = y} = 0) :
    ∀ᵐ h ∂(Measure.pi μ).map (supportSingleObservation u), ∀ i, i ≠ h.1 →
      supportPosteriorShift μ u i h = halfspacePosteriorShift (μ i) u h.2 := by
  filter_upwards [supportSelectionKernel_ae_eq_condDistrib μ u] with h hh
  intro i hni
  unfold supportPosteriorShift
  rw [← hh]
  have he := integral_map_of_stronglyMeasurable (μ := supportSelectionKernel μ u h)
    (measurable_pi_apply i)
    (stronglyMeasurable_id.sub (stronglyMeasurable_const (b := ∫ z : E, z ∂μ i)))
  rw [supportSelectionKernel_coordinate,
    supportSelection_loser_halfspace_kernel_mixed μ u h.1 i hni (hD i) h.2] at he
  exact he.symm

end
end Nonsmooth
