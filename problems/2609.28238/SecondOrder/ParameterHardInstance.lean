import SecondOrder.ParameterizedKernelLaw

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

universe u
namespace SecondOrder
noncomputable section
variable {H S A : Type u} [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace A]

/-- A small actual mixture success probability supplies one fixed hidden
parameter against the same randomized algorithm and private seed law. -/
theorem parameterized_exists_hard_event (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (H × FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)]
    (N : ℕ) {E : Set (H × FiniteHistory S A N)} (hE : MeasurableSet E)
    (hb : (adaptiveKernelLaw (ρ.prod μ) (parameterizedResponseKernel K) N).real
      {h | ((finiteHistoryInitial N h).1,finiteHistoryMapInitial Prod.snd N h) ∈ E}≤1/8) :
    ∃ θ, (adaptiveKernelLaw μ (fun n => (K n).sectR θ) N).real {h | (θ,h) ∈ E}<(1:ℝ)/4 := by
  have he := adaptiveKernelLaw_parameter_event ρ μ K N hE
  have hu := ENNReal.ofReal_le_ofReal hb
  simp only [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] at hu
  rw [he] at hu
  by_contra hn
  have hl : ∀ θ, (1:ℝ)/4≤(adaptiveKernelLaw μ (fun n => (K n).sectR θ) N).real {h | (θ,h) ∈ E} := by
    simpa only [not_exists,not_lt] using hn
  have hi : (∫⁻ _θ, ENNReal.ofReal ((1:ℝ)/4) ∂ρ)≤
      ∫⁻ θ, adaptiveKernelLaw μ (fun n => (K n).sectR θ) N {h | (θ,h) ∈ E} ∂ρ := by
    apply lintegral_mono
    intro θ
    have hh := ENNReal.ofReal_le_ofReal (hl θ)
    simpa only [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] using hh
  have hh := hi.trans hu
  norm_num at hh

end
end SecondOrder
