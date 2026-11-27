import Nonsmooth.ParametricEventKernel

open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {k : ℕ}

def supportLoserRegion (u : E) (i : Fin k) : Set ((Fin k × ℝ) × E) :=
  {z | ⟪z.2, u⟫_ℝ ≤ z.1.2 ∧ (¬i < z.1.1 ∨ ⟪z.2, u⟫_ℝ < z.1.2)}

theorem supportLoserRegion_measurable (u : E) (i : Fin k) : MeasurableSet (supportLoserRegion u i) := by
  have hvalue : Measurable (fun z : (Fin k × ℝ) × E => ⟪z.2, u⟫_ℝ) :=
    (continuous_snd.inner continuous_const).measurable
  have hindex : MeasurableSet {z : (Fin k × ℝ) × E | i < z.1.1} :=
    (measurable_fst.fst) ((Set.to_countable {w : Fin k | i < w}).measurableSet)
  exact (measurableSet_le hvalue measurable_fst.snd).inter
    (hindex.compl.union (measurableSet_lt hvalue measurable_fst.snd))

/-- The winner uses a regular projection slice; all other rows use the strict/non-strict loser event. -/
def supportSelectionRowKernel (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (u : E) (i : Fin k) : Kernel (Fin k × ℝ) E := by
  classical
  exact Kernel.piecewise (measurable_fst (measurableSet_singleton i))
    (Kernel.comap (condDistrib id (fun z : E => ⟪z, u⟫_ℝ) (μ i)) Prod.snd measurable_snd)
    (parametricEventKernel (μ i) (supportLoserRegion u i) (supportLoserRegion_measurable u i))

instance supportSelectionRowKernel_markov (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (u : E) (i : Fin k) : IsMarkovKernel (supportSelectionRowKernel μ u i) := by
  unfold supportSelectionRowKernel
  infer_instance

/-- The measurable product posterior; `SelectionPosterior` proves its disintegration identity. -/
def supportSelectionKernel (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (u : E) : Kernel (Fin k × ℝ) (Fin k → E) :=
  finiteProductKernel (supportSelectionRowKernel μ u)

instance supportSelectionKernel_markov (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (u : E) : IsMarkovKernel (supportSelectionKernel μ u) := by
  unfold supportSelectionKernel
  infer_instance

theorem supportSelectionRowKernel_winner (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (u : E) (w : Fin k) (y : ℝ) :
    supportSelectionRowKernel μ u w (w, y) = condDistrib id (fun z : E => ⟪z, u⟫_ℝ) (μ w) y := by
  simp [supportSelectionRowKernel, Kernel.piecewise_apply, Kernel.comap_apply]

theorem supportSelectionRowKernel_loser (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (u : E) (w i : Fin k) (hi : i ≠ w) (y : ℝ)
    (hpos : μ i (Prod.mk (w, y) ⁻¹' supportLoserRegion u i) ≠ 0) :
    supportSelectionRowKernel μ u i (w, y) = (μ i)[|Prod.mk (w, y) ⁻¹' supportLoserRegion u i] := by
  classical
  rw [supportSelectionRowKernel, Kernel.piecewise_apply]
  simp only [mem_preimage, mem_singleton_iff, Ne.symm hi, if_false]
  exact parametricEventKernel_apply _ _ _ _ hpos

theorem supportSelectionKernel_coordinate (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (u : E) (w : Fin k) (y : ℝ) (i : Fin k) :
    (supportSelectionKernel μ u (w, y)).map (fun a : Fin k → E => a i) = supportSelectionRowKernel μ u i (w, y) :=
  finiteProductKernel_coordinate _ _ _

theorem supportSelectionKernel_independent (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (u : E) (w : Fin k) (y : ℝ) :
    iIndepFun (fun i (a : Fin k → E) => a i) (supportSelectionKernel μ u (w, y)) :=
  finiteProductKernel_independent _ _

end
end Nonsmooth
