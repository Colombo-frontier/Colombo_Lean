import Nonsmooth.SelectionDisintegration
import Mathlib.Probability.Kernel.Composition.MeasureComp

open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

theorem finite_pi_measure_ext {β : Type} [MeasurableSpace β] {k : ℕ}
    (μ ν : Measure (Fin k → β)) [IsFiniteMeasure μ]
    (h : ∀ (A : Fin k → Set β), (∀ i, MeasurableSet (A i)) →
      μ (Set.univ.pi A) = ν (Set.univ.pi A)) : μ = ν := by
  apply ext_of_generate_finite _ generateFrom_pi.symm isPiSystem_pi
  · rintro _ ⟨A, hA, rfl⟩
    exact h A (fun i => hA i (mem_univ i))
  · simpa only [pi_univ] using h (fun _ => Set.univ) (fun _ => MeasurableSet.univ)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {n : ℕ}

/-- Extension of the one-observation disintegration identity to every measurable row event. -/
theorem supportSelectionKernel_disintegration_set
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (u : E) (w : Fin (n + 1)) {D : Set ℝ} (hD : MeasurableSet D)
    {B : Set (Fin (n + 1) → E)} (hB : MeasurableSet B) :
    Measure.pi μ ({a : Fin (n + 1) → E | supportWinner a u = w ∧ finiteSupport a u ∈ D} ∩ B) =
      ∫⁻ y in D, supportSelectionKernel μ u (w, y) B ∂supportSelectionValueLaw μ u w := by
  let H : Set (Fin (n + 1) → E) := {a | supportWinner a u = w ∧ finiteSupport a u ∈ D}
  let κ : Kernel ℝ (Fin (n + 1) → E) :=
    Kernel.comap (supportSelectionKernel μ u) (fun y => (w, y)) (measurable_const.prodMk measurable_id)
  have he : (Measure.pi μ).restrict H = κ ∘ₘ ((supportSelectionValueLaw μ u w).restrict D) := by
    apply finite_pi_measure_ext
    intro A hA
    rw [Measure.restrict_apply (MeasurableSet.univ_pi hA),
      Measure.bind_apply (MeasurableSet.univ_pi hA) κ.aemeasurable]
    have hs : Set.univ.pi A ∩ H =
        {a : Fin (n + 1) → E | supportWinner a u = w ∧ finiteSupport a u ∈ D ∧ ∀ i, a i ∈ A i} := by
      ext a
      constructor
      · rintro ⟨ha, hw, hy⟩
        exact ⟨hw, hy, fun i => ha i (mem_univ i)⟩
      · rintro ⟨hw, hy, ha⟩
        exact ⟨fun i _ => ha i, hw, hy⟩
    rw [hs, supportSelectionKernel_disintegration_rectangle μ u w hD A hA]
    rfl
  have h := congrArg (fun ν : Measure (Fin (n + 1) → E) => ν B) he
  rw [Measure.restrict_apply hB, Measure.bind_apply hB κ.aemeasurable, inter_comm] at h
  exact h

end
end Nonsmooth
