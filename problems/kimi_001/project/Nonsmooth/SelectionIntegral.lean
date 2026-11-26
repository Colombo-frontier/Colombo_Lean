import Nonsmooth.SelectionGeometry

open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem support_selection_event_measurable {k : ℕ} [Nonempty (Fin k)]
    (u : E) (w : Fin k) {D : Set ℝ} (hD : MeasurableSet D)
    (A : Fin k → Set E) (hA : ∀ i, MeasurableSet (A i)) :
    MeasurableSet {a : Fin k → E | supportWinner a u = w ∧ finiteSupport a u ∈ D ∧ ∀ i, a i ∈ A i} := by
  have he : {a : Fin k → E | supportWinner a u = w ∧ finiteSupport a u ∈ D ∧ ∀ i, a i ∈ A i} =
      {a | a w ∈ A w ∧ ⟪a w, u⟫_ℝ ∈ D ∧ ∀ i, i ≠ w →
        a i ∈ A i ∩ Prod.mk (w, ⟪a w, u⟫_ℝ) ⁻¹' supportLoserRegion u i} := by
    ext a
    exact support_selection_rectangle a u w D A
  rw [he]
  have hm : Measurable (fun a : Fin k → E => ⟪a w, u⟫_ℝ) :=
    ((continuous_apply w).inner continuous_const).measurable
  refine ((measurable_pi_apply w) (hA w)).inter ((hm hD).inter ?_)
  have hall (i : Fin k) : MeasurableSet {a : Fin k → E | i ≠ w →
      a i ∈ A i ∩ Prod.mk (w, ⟪a w, u⟫_ℝ) ⁻¹' supportLoserRegion u i} := by
    by_cases hi : i ≠ w
    · have hp : Measurable (fun a : Fin k → E => ((w, ⟪a w, u⟫_ℝ), a i)) :=
        (measurable_const.prodMk hm).prodMk (measurable_pi_apply i)
      have hb := ((measurable_pi_apply i) (hA i)).inter (hp (supportLoserRegion_measurable u i))
      convert hb using 1
      ext a
      exact ⟨fun h => h hi, fun h _ => h⟩
    · have heq : {a : Fin k → E | i ≠ w →
          a i ∈ A i ∩ Prod.mk (w, ⟪a w, u⟫_ℝ) ⁻¹' supportLoserRegion u i} = Set.univ := by
        ext a
        exact ⟨fun _ => mem_univ a, fun _ h => (hi h).elim⟩
      rw [heq]
      exact MeasurableSet.univ
  convert MeasurableSet.iInter hall using 1
  ext a
  simp only [Set.mem_iInter, Set.mem_setOf_eq]
  rfl

/-- Exact Fubini decomposition of a maximum-observation rectangle by its winning row. -/
theorem independent_support_selection_integral {n : ℕ}
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (u : E) (w : Fin (n + 1)) {D : Set ℝ} (hD : MeasurableSet D)
    (A : Fin (n + 1) → Set E) (hA : ∀ i, MeasurableSet (A i)) :
    Measure.pi μ {a : Fin (n + 1) → E | supportWinner a u = w ∧ finiteSupport a u ∈ D ∧ ∀ i, a i ∈ A i} =
      ∫⁻ z in A w ∩ (fun z : E => ⟪z, u⟫_ℝ) ⁻¹' D,
        ∏ j : Fin n, μ (w.succAbove j) (A (w.succAbove j) ∩
          (Prod.mk (w, ⟪z, u⟫_ℝ) ⁻¹' supportLoserRegion u (w.succAbove j))) ∂μ w := by
  classical
  let H : Set (Fin (n + 1) → E) :=
    {a | supportWinner a u = w ∧ finiteSupport a u ∈ D ∧ ∀ i, a i ∈ A i}
  let Z : Set E := A w ∩ (fun z : E => ⟪z, u⟫_ℝ) ⁻¹' D
  let B (z : E) (j : Fin n) : Set E := A (w.succAbove j) ∩
    (Prod.mk (w, ⟪z, u⟫_ℝ) ⁻¹' supportLoserRegion u (w.succAbove j))
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) w
  have hH : MeasurableSet H := support_selection_event_measurable u w hD A hA
  have hZ : MeasurableSet Z := (hA w).inter ((continuous_id.inner continuous_const).measurable hD)
  have hp := (measurePreserving_piFinSuccAbove μ w).symm
  have hmap := congrArg (fun ν : Measure (Fin (n + 1) → E) => ν H) hp.map_eq
  rw [Measure.map_apply e.symm.measurable hH] at hmap
  change Measure.pi μ H = _
  rw [← hmap, Measure.prod_apply (e.symm.measurable hH)]
  have hsection (z : E) : Prod.mk z ⁻¹' (e.symm ⁻¹' H) = if z ∈ Z then Set.univ.pi (B z) else ∅ := by
    ext b
    change (supportWinner (w.insertNth z b) u = w ∧ finiteSupport (w.insertNth z b) u ∈ D ∧
      ∀ i : Fin (n + 1), (w.insertNth z b : Fin (n + 1) → E) i ∈ A i) ↔ _
    rw [support_selection_insertNth]
    by_cases hz : z ∈ Z
    · rw [if_pos hz]
      exact ⟨fun h => h.2.2, fun hb => ⟨hz.1, hz.2, hb⟩⟩
    · rw [if_neg hz]
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨hzA, hzD, _⟩
      exact hz ⟨hzA, hzD⟩
  change (∫⁻ z, Measure.pi (fun j : Fin n => μ (w.succAbove j)) (Prod.mk z ⁻¹' (e.symm ⁻¹' H)) ∂μ w) =
    ∫⁻ z in Z, ∏ j : Fin n, μ (w.succAbove j) (B z j) ∂μ w
  rw [← lintegral_indicator hZ]
  apply lintegral_congr
  intro z
  rw [hsection]
  by_cases hz : z ∈ Z
  · rw [if_pos hz, Set.indicator_of_mem hz, Measure.pi_pi]
  · rw [if_neg hz, Set.indicator_of_notMem hz, measure_empty]

end
end Nonsmooth
