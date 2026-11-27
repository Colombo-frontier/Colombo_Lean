import Nonsmooth.SelectionIntegral
import Nonsmooth.ProjectionSlice

open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {n : ℕ}

def supportSelectionWeight (μ : Fin (n + 1) → Measure E) (u : E)
    (w : Fin (n + 1)) (y : ℝ) : ℝ≥0∞ :=
  ∏ j : Fin n, μ (w.succAbove j) (Prod.mk (w, y) ⁻¹' supportLoserRegion u (w.succAbove j))

theorem supportSelectionWeight_measurable (μ : Fin (n + 1) → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)] (u : E) (w : Fin (n + 1)) :
    Measurable (supportSelectionWeight μ u w) := by
  apply Finset.measurable_prod
  intro j _
  exact (measurable_measure_prodMk_left (supportLoserRegion_measurable u (w.succAbove j))).comp
    (measurable_const.prodMk measurable_id)

def supportSelectionValueLaw (μ : Fin (n + 1) → Measure E) (u : E)
    (w : Fin (n + 1)) : Measure ℝ :=
  ((μ w).map (fun z : E => ⟪z, u⟫_ℝ)).withDensity (supportSelectionWeight μ u w)

theorem supportSelectionRowKernel_loser_weighted {k : ℕ}
    (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (u : E) (w i : Fin k) (hi : i ≠ w) (y : ℝ) (A : Set E) :
    μ i (Prod.mk (w, y) ⁻¹' supportLoserRegion u i) *
      supportSelectionRowKernel μ u i (w, y) A =
      μ i (A ∩ (Prod.mk (w, y) ⁻¹' supportLoserRegion u i)) := by
  classical
  rw [supportSelectionRowKernel, Kernel.piecewise_apply]
  simp only [mem_preimage, mem_singleton_iff, Ne.symm hi, if_false]
  rw [parametricEventKernel_weighted_apply, inter_comm]

theorem supportSelectionKernel_weighted_rectangle
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (u : E) (w : Fin (n + 1)) (y : ℝ) (A : Fin (n + 1) → Set E) :
    supportSelectionWeight μ u w y * supportSelectionKernel μ u (w, y) (Set.univ.pi A) =
      (∏ j : Fin n, μ (w.succAbove j) (A (w.succAbove j) ∩
        (Prod.mk (w, y) ⁻¹' supportLoserRegion u (w.succAbove j)))) *
      condDistrib id (fun z : E => ⟪z, u⟫_ℝ) (μ w) y (A w) := by
  rw [supportSelectionKernel, finiteProductKernel_rectangle,
    Fin.prod_univ_succAbove _ w, supportSelectionRowKernel_winner]
  unfold supportSelectionWeight
  rw [mul_left_comm, ← Finset.prod_mul_distrib]
  simp_rw [supportSelectionRowKernel_loser_weighted μ u w _ (w.succAbove_ne _) y]
  exact mul_comm _ _

/-- The product kernel gives the exact joint law of one maximum observation and any row rectangle. -/
theorem supportSelectionKernel_disintegration_rectangle
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (u : E) (w : Fin (n + 1)) {D : Set ℝ} (hD : MeasurableSet D)
    (A : Fin (n + 1) → Set E) (hA : ∀ i, MeasurableSet (A i)) :
    Measure.pi μ {a : Fin (n + 1) → E | supportWinner a u = w ∧ finiteSupport a u ∈ D ∧ ∀ i, a i ∈ A i} =
      ∫⁻ y in D, supportSelectionKernel μ u (w, y) (Set.univ.pi A) ∂supportSelectionValueLaw μ u w := by
  let g : ℝ → ℝ≥0∞ := fun y => ∏ j : Fin n, μ (w.succAbove j)
    (A (w.succAbove j) ∩ Prod.mk (w, y) ⁻¹' supportLoserRegion u (w.succAbove j))
  have hg : Measurable g := by
    apply Finset.measurable_prod
    intro j _
    have hm := measurable_measure_prodMk_left (ν := μ (w.succAbove j))
      ((measurable_snd (hA (w.succAbove j))).inter (supportLoserRegion_measurable u (w.succAbove j)))
    exact hm.comp (measurable_const.prodMk measurable_id)
  rw [independent_support_selection_integral μ u w hD A hA,
    projection_slice_weighted_integral (μ w) (fun z : E => ⟪z, u⟫_ℝ)
      (continuous_id.inner continuous_const).measurable (hA w) hD g hg]
  have hk : Measurable (fun y : ℝ => supportSelectionKernel μ u (w, y) (Set.univ.pi A)) :=
    ((Kernel.measurable_coe (supportSelectionKernel μ u) (MeasurableSet.univ_pi hA)).comp
      (measurable_const.prodMk measurable_id))
  rw [supportSelectionValueLaw, setLIntegral_withDensity_eq_setLIntegral_mul _
    (supportSelectionWeight_measurable μ u w) hk hD]
  apply lintegral_congr
  intro y
  exact (supportSelectionKernel_weighted_rectangle μ u w y A).symm

theorem supportSelectionValueLaw_apply
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (u : E) (w : Fin (n + 1)) {D : Set ℝ} (hD : MeasurableSet D) :
    supportSelectionValueLaw μ u w D =
      Measure.pi μ {a : Fin (n + 1) → E | supportWinner a u = w ∧ finiteSupport a u ∈ D} := by
  have h := supportSelectionKernel_disintegration_rectangle μ u w hD
    (fun _ => Set.univ) (fun _ => MeasurableSet.univ)
  simpa only [mem_univ, implies_true, and_true, pi_univ, measure_univ,
    lintegral_const, one_mul, Measure.restrict_apply_univ] using h.symm

end
end Nonsmooth
