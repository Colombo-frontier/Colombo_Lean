import Bilevel.PolishedHistoryDeterministicRepresentation
import Bilevel.StochasticOuter

/-! The only private randomness required by the upper-bound solver is a
fresh independent terminal output index. It is sampled after the adaptive
oracle experiment. Joint output-law preservation therefore transports both
the selected-output risk and the original-call budget. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
set_option autoImplicit false
variable {I U V Y Z : Type*} [MeasurableSpace I] [MeasurableSpace U]
  [MeasurableSpace V] [MeasurableSpace Y] [MeasurableSpace Z]

theorem independent_terminal_pair_law (ρ : Measure I) (μ : Measure U)
    [SFinite ρ] [SFinite μ] (output : U → Y) (ho : Measurable output) :
    (ρ.prod μ).map (fun z => (z.1,output z.2))=ρ.prod (μ.map output) := by
  simpa only [Measure.map_id] using
    (Measure.map_prod_map ρ μ measurable_id ho).symm

/-- Equality of the body output law permits an arbitrary measurable pure
terminal selector under a genuinely independent private index. -/
theorem independent_terminal_selection_law
    (ρ : Measure I) (μ : Measure U) (ν : Measure V)
    [SFinite ρ] [SFinite μ] [SFinite ν]
    (outμ : U → Y) (outν : V → Y) (hμ : Measurable outμ) (hν : Measurable outν)
    (hout : μ.map outμ=ν.map outν)
    (select : I × Y → Z) (hselect : Measurable select) :
    (ρ.prod μ).map (fun z => select (z.1,outμ z.2))=
      (ρ.prod ν).map (fun z => select (z.1,outν z.2)) := by
  have hpμ : Measurable (fun z : I × U => (z.1,outμ z.2)) :=
    measurable_fst.prodMk (hμ.comp measurable_snd)
  have hpν : Measurable (fun z : I × V => (z.1,outν z.2)) :=
    measurable_fst.prodMk (hν.comp measurable_snd)
  calc
    _ = ((ρ.prod μ).map (fun z => (z.1,outμ z.2))).map select :=
      (Measure.map_map hselect hpμ).symm
    _ = (ρ.prod (μ.map outμ)).map select := by rw [independent_terminal_pair_law ρ μ outμ hμ]
    _ = (ρ.prod (ν.map outν)).map select := by rw [hout]
    _ = ((ρ.prod ν).map (fun z => (z.1,outν z.2))).map select := by
      rw [independent_terminal_pair_law ρ ν outν hν]
    _ = _ := Measure.map_map hselect hpν

/-- Sampling a terminal private index adds no original SFO calls. -/
theorem independent_terminal_cost (ρ : Measure I) [IsProbabilityMeasure ρ]
    (μ : Measure U) [SFinite μ] (cost : U → ℝ≥0∞) (hc : Measurable cost) :
    (∫⁻ z : I × U,cost z.2 ∂ρ.prod μ)=∫⁻ u,cost u ∂μ := by
  have hm : Measurable (fun z : I × U => cost z.2) := hc.comp measurable_snd
  rw [lintegral_prod _ hm.aemeasurable]
  simp only [lintegral_const,measure_univ,one_mul,mul_one]

/-- The independent terminal index is exactly uniform, with the actual
expectation equal to the average over the body experiment's outputs. -/
theorem terminal_uniform_integral (n : ℕ) [NeZero n]
    (μ : Measure U) [IsProbabilityMeasure μ] (loss : Fin n × U → ℝ)
    (hloss : Integrable loss ((StochasticOuter.uniformLaw n).prod μ)) :
    (∫ z,loss z ∂(StochasticOuter.uniformLaw n).prod μ)=
      (∑ i : Fin n,∫ u,loss (i,u) ∂μ)/(n:ℝ) := by
  rw [integral_prod _ hloss,StochasticOuter.uniform_integral]

end Bilevel.PolishedHistory
