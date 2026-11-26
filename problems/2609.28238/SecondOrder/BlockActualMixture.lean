import SecondOrder.BlockComparisonKernel
import SecondOrder.ParameterHardInstance

open MeasureTheory ProbabilityTheory
open scoped Classical

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSpace S] [MeasurableSpace A]

def blockActualParameterKernel (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) (n : ℕ) : Kernel ((Fin T → H) × FiniteHistory S A n) A :=
  (indexedResponseKernel O).comap
    (fun z => ((z.1,query n z.2),blockActivationIndex active z.1 (query n z.2) T))
    ((measurable_fst.prodMk ((hq n).comp measurable_snd)).prodMk
      (blockActivationIndex_measurable active ha Prod.fst (query n ∘ Prod.snd) (fun _ => T)
        (fun i => (measurable_pi_apply i).comp measurable_fst) ((hq n).comp measurable_snd) measurable_const))

instance blockActualParameterKernel_markov (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)] (n : ℕ) :
    IsMarkovKernel (blockActualParameterKernel active ha query hq O n) := by
  unfold blockActualParameterKernel
  infer_instance

def blockActualFixedKernel (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) (Θ : Fin T → H) (n : ℕ) :
    Kernel (FiniteHistory S A n) A := (blockActualParameterKernel active ha query hq O n).sectR Θ

instance blockActualFixedKernel_markov (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)] (Θ : Fin T → H) (n : ℕ) :
    IsMarkovKernel (blockActualFixedKernel active ha query hq O Θ n) := by
  unfold blockActualFixedKernel
  infer_instance

theorem blockActualFixedKernel_apply (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) (Θ : Fin T → H) (n : ℕ) (h : FiniteHistory S A n) :
    blockActualFixedKernel active ha query hq O Θ n h=
      O (blockActivationIndex active Θ (query n h) T) (Θ,query n h) := rfl

theorem blockActualKernel_parameterized (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) :
    blockActualKernel active ha query hq O=parameterizedResponseKernel (blockActualParameterKernel active ha query hq O) := by
  funext n
  apply Kernel.ext
  intro h
  rfl

theorem blockActual_exists_hard_event (ρ : Fin T → Measure H) [∀ i, IsProbabilityMeasure (ρ i)]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)] (N : ℕ)
    {E : Set ((Fin T → H) × FiniteHistory S A N)} (hE : MeasurableSet E)
    (hb : (adaptiveKernelLaw ((Measure.pi ρ).prod μ) (blockActualKernel active ha query hq O) N).real
      {h | ((finiteHistoryInitial N h).1,finiteHistoryMapInitial Prod.snd N h) ∈ E}≤1/8) :
    ∃ Θ, (adaptiveKernelLaw μ (blockActualFixedKernel active ha query hq O Θ) N).real {h | (Θ,h) ∈ E}<(1:ℝ)/4 := by
  rw [blockActualKernel_parameterized] at hb
  exact parameterized_exists_hard_event (Measure.pi ρ) μ (blockActualParameterKernel active ha query hq O) N hE hb

end
end SecondOrder
