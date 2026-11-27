import Nonsmooth.AERankControlledSelection
import Nonsmooth.SupportAggregateCriterion

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def projectionPosteriorShift (μ : Measure E) [IsProbabilityMeasure μ] (u : E) (y : ℝ) : E :=
  ∫ z : E, (z - ∫ a : E, a ∂μ) ∂condDistrib id (fun z : E => ⟪z, u⟫_ℝ) μ y

theorem projectionPosteriorShift_measurable (μ : Measure E) [IsProbabilityMeasure μ] (u : E) :
    Measurable (projectionPosteriorShift μ u) := by
  have hf : StronglyMeasurable (fun z : E => z - ∫ a : E, a ∂μ) :=
    stronglyMeasurable_id.sub stronglyMeasurable_const
  exact hf.integral_kernel.measurable

theorem supportWinnerShiftEnergy_measurable {k : ℕ} [Nonempty (Fin k)]
    (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E) :
    Measurable (supportWinnerShiftEnergy μ u) := by
  have hm : Measurable (fun p : (Fin k × ℝ) × Fin k => supportPosteriorShift μ u p.2 p.1) :=
    measurable_from_prod_countable_left (fun i => supportPosteriorShift_measurable μ u i)
  exact ((hm.comp (measurable_id.prodMk measurable_fst)).norm).pow_const 2

theorem supportPosteriorShift_winner_ae {n : ℕ}
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E) :
    ∀ᵐ h ∂(Measure.pi μ).map (supportSingleObservation u),
      supportPosteriorShift μ u h.1 h = projectionPosteriorShift (μ h.1) u h.2 := by
  filter_upwards [supportSelectionKernel_ae_eq_condDistrib μ u] with h hh
  unfold supportPosteriorShift
  rw [← hh]
  have he := integral_map_of_stronglyMeasurable (μ := supportSelectionKernel μ u h)
    (measurable_pi_apply h.1)
    (stronglyMeasurable_id.sub (stronglyMeasurable_const (b := ∫ z : E, z ∂μ h.1)))
  rw [supportSelectionKernel_coordinate, supportSelectionRowKernel_winner] at he
  exact he.symm

/-- An almost-everywhere rank bound for the actual one-row projection posterior
gives a logarithmic energy bound for the actual winning row after max/index observation. -/
theorem support_winner_energy_of_projection_rank {n : ℕ}
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E)
    (hzero : ∀ i y, μ i {z : E | ⟪z, u⟫_ℝ = y} = 0) {K : ℝ} (hK : 0 < K)
    (hrank : ∀ i, ∀ᵐ y ∂(μ i).map (fun z : E => ⟪z, u⟫_ℝ),
      ‖projectionPosteriorShift (μ i) u y‖ ^ 2 ≤
        K * (1 + rankQuantileLog (cdf ((μ i).map (fun z : E => ⟪z, u⟫_ℝ)) y))) :
    Integrable (supportWinnerShiftEnergy μ u) ((Measure.pi μ).map (supportSingleObservation u)) ∧
      (∫ h, supportWinnerShiftEnergy μ u h ∂(Measure.pi μ).map (supportSingleObservation u)) ≤
        K * (1 + 2 * Real.log (4 * ((n + 1 : ℕ) : ℝ))) := by
  let Q := Measure.pi μ
  let X : Fin (n + 1) → (Fin (n + 1) → E) → ℝ := fun i a => ⟪a i, u⟫_ℝ
  let W : (Fin (n + 1) → E) → Fin (n + 1) := fun a => supportWinner a u
  let f : Fin (n + 1) → ℝ → ℝ := fun i y => ‖projectionPosteriorShift (μ i) u y‖ ^ 2
  let Z : (Fin (n + 1) → E) → ℝ := fun a => f (W a) (X (W a) a)
  have hu : Measurable (fun z : E => ⟪z, u⟫_ℝ) := (continuous_id.inner continuous_const).measurable
  have hX (i : Fin (n + 1)) : Measurable (X i) := hu.comp (measurable_pi_apply i)
  have hf (i : Fin (n + 1)) : Measurable (f i) := (projectionPosteriorShift_measurable (μ i) u).norm.pow_const 2
  have hpair : Measurable (fun a : Fin (n + 1) → E => (a, u)) :=
    measurable_id.prodMk measurable_const
  have hW : Measurable W := by
    simpa only [Function.comp_def, W] using
      (supportWinner_measurable (E := E) (k := n + 1)).comp hpair
  have hZ : Measurable Z := by
    have hm : Measurable (fun p : (Fin (n + 1) → E) × Fin (n + 1) => f p.2 (X p.2 p.1)) :=
      measurable_from_prod_countable_left (fun i => (hf i).comp (hX i))
    simpa only [Function.comp_def, id_eq, Z] using hm.comp (measurable_id.prodMk hW)
  have hmap (i : Fin (n + 1)) : Q.map (X i) = (μ i).map (fun z : E => ⟪z, u⟫_ℝ) := by
    have hh := congrArg (fun ν : Measure E => ν.map (fun z : E => ⟪z, u⟫_ℝ)) (product_row_coordinate_law μ i)
    try dsimp only at hh
    rw [Measure.map_map hu (measurable_pi_apply i)] at hh
    exact hh
  have hbound := selected_rank_controlled_energy_ae Q X hX
    (fun i y => by rw [hmap i, Measure.map_apply hu (measurableSet_singleton y)]; exact hzero i y)
    f hf hK (fun i => by rw [hmap i]; exact hrank i) Z hZ (fun a => sq_nonneg _)
    (fun a => ⟨W a, le_rfl⟩)
  have hO := supportSingleObservation_measurable (E := E) (k := n + 1) u
  have hae := ae_of_ae_map hO.aemeasurable (supportPosteriorShift_winner_ae μ u)
  have heq : (fun a => supportWinnerShiftEnergy μ u (supportSingleObservation u a)) =ᵐ[Q] Z := by
    filter_upwards [hae] with a ha
    change supportPosteriorShift μ u (supportWinner a u) (supportSingleObservation u a) =
      projectionPosteriorShift (μ (supportWinner a u)) u (finiteSupport a u) at ha
    change ‖supportPosteriorShift μ u (supportWinner a u) (supportSingleObservation u a)‖ ^ 2 = _
    rw [ha]
    rw [supportWinner_attained]
  have hraw : Integrable (fun a => supportWinnerShiftEnergy μ u (supportSingleObservation u a)) Q :=
    hbound.1.congr heq.symm
  have hm : Measurable (supportWinnerShiftEnergy μ u) := supportWinnerShiftEnergy_measurable μ u
  have hi : Integrable (supportWinnerShiftEnergy μ u) (Q.map (supportSingleObservation u)) :=
    (integrable_map_measure (g := supportWinnerShiftEnergy μ u) (f := supportSingleObservation u) (μ := Q)
      hm.aestronglyMeasurable hO.aemeasurable).mpr hraw
  constructor
  · exact hi
  · have hh := integral_map_of_stronglyMeasurable (μ := Q) hO hm.stronglyMeasurable
    exact hh.trans (integral_congr_ae heq) |>.trans_le hbound.2

end
end Nonsmooth
