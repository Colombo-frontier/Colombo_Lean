import SecondOrder.BlockTargetKernel
import SecondOrder.ParameterizedKernelLaw

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSpace S] [MeasurableSpace A]

def blockParameterKernel (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) (n : ℕ) :
    Kernel ((Fin T → H) × FiniteHistory S A n) A :=
  (indexedResponseKernel O).comap
    (fun z => ((z.1,query n z.2),blockComparisonIndex active query z.1 n z.2))
    ((measurable_fst.prodMk ((hq n).comp measurable_snd)).prodMk
      (blockComparisonIndex_measurable active ha query hq n))

instance blockParameterKernel_markov (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)] (n : ℕ) :
    IsMarkovKernel (blockParameterKernel active ha query hq O n) := by
  unfold blockParameterKernel
  infer_instance

theorem blockComparisonKernel_parameterized (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) :
    blockComparisonKernel active ha query hq O=parameterizedResponseKernel (blockParameterKernel active ha query hq O) := by
  funext n
  apply Kernel.ext
  intro h
  rfl

theorem blockFixedKernel_section (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) (Θ : Fin T → H) :
    blockFixedKernel active ha query hq O Θ=fun n => (blockParameterKernel active ha query hq O n).sectR Θ := by
  funext n
  apply Kernel.ext
  intro h
  rfl

theorem blockComparison_probability_mixture (ρ : Measure (Fin T → H)) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (n : ℕ) {E : Set ((Fin T → H) × FiniteHistory S A n)} (hE : MeasurableSet E) :
    adaptiveKernelLaw (ρ.prod μ) (blockComparisonKernel active ha query hq O) n
      {h | ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h) ∈ E} =
      ∫⁻ Θ, adaptiveKernelLaw μ (blockFixedKernel active ha query hq O Θ) n {h | (Θ,h) ∈ E} ∂ρ := by
  simp_rw [blockComparisonKernel_parameterized,blockFixedKernel_section]
  exact adaptiveKernelLaw_parameter_event ρ μ _ n hE

theorem blockFixed_probability_measurable (μ : Measure S) [IsProbabilityMeasure μ]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (n : ℕ) {E : Set ((Fin T → H) × FiniteHistory S A n)} (hE : MeasurableSet E) :
    Measurable (fun Θ => adaptiveKernelLaw μ (blockFixedKernel active ha query hq O Θ) n {h | (Θ,h) ∈ E}) := by
  simp_rw [blockFixedKernel_section]
  exact parameterHistory_event_measurable μ _ n hE

def blockTargetParameterKernel (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) (Θ : Fin T → H) (j : Fin T) (n : ℕ) :
    Kernel (H × FiniteHistory S A n) A :=
  (blockParameterKernel active ha query hq O n).comap
    (fun z => (Function.update Θ j z.1,z.2))
    (((measurable_update Θ).comp measurable_fst).prodMk measurable_snd)

instance blockTargetParameterKernel_markov (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (Θ : Fin T → H) (j : Fin T) (n : ℕ) : IsMarkovKernel (blockTargetParameterKernel active ha query hq O Θ j n) := by
  unfold blockTargetParameterKernel
  infer_instance

theorem blockTargetKernel_parameterized (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) (Θ : Fin T → H) (j : Fin T) :
    blockTargetKernel active ha query hq O Θ j=parameterizedResponseKernel (blockTargetParameterKernel active ha query hq O Θ j) := by
  funext n
  apply Kernel.ext
  intro h
  rw [blockTargetKernel_apply]
  rfl

theorem blockTargetParameterKernel_section (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) (Θ : Fin T → H) (j : Fin T) (θ : H) :
    (fun n => (blockTargetParameterKernel active ha query hq O Θ j n).sectR θ)=
      blockFixedKernel active ha query hq O (Function.update Θ j θ) := by
  funext n
  apply Kernel.ext
  intro h
  rfl

theorem blockTarget_probability_mixture (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (Θ : Fin T → H) (j : Fin T) (n : ℕ)
    {E : Set ((Fin T → H) × FiniteHistory S A n)} (hE : MeasurableSet E) :
    adaptiveKernelLaw (ρ.prod μ) (blockTargetKernel active ha query hq O Θ j) n
      {h | (Function.update Θ j (finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h) ∈ E} =
      ∫⁻ θ, adaptiveKernelLaw μ (blockFixedKernel active ha query hq O (Function.update Θ j θ)) n
        {h | (Function.update Θ j θ,h) ∈ E} ∂ρ := by
  rw [blockTargetKernel_parameterized]
  have hE' : MeasurableSet {z : H × FiniteHistory S A n | (Function.update Θ j z.1,z.2) ∈ E} :=
    hE.preimage (((measurable_update Θ).comp measurable_fst).prodMk measurable_snd)
  have he := adaptiveKernelLaw_parameter_event ρ μ (blockTargetParameterKernel active ha query hq O Θ j) n
    hE'
  simpa only [blockTargetParameterKernel_section,Set.mem_setOf_eq] using he

end
end SecondOrder
