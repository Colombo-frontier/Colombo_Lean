import SecondOrder.SequentialConstants
import SecondOrder.BlockActualMixture

open MeasureTheory ProbabilityTheory InformationTheory
open scoped Classical ENNReal

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSpace S] [MeasurableSpace A]

/-- Prefix dependence is substantive only below the final block index.
At and above it the hypothesis already fixes every hidden coordinate. -/
theorem blockKernel_prefix_of_bounded (O : ℕ → Kernel ((Fin T → H) × X) A)
    (hO : ∀ p, p<T → ∀ Θ Θ' x, (∀ i : Fin T, i.val<p+1 → Θ i=Θ' i) → O p (Θ,x)=O p (Θ',x)) :
    ∀ p Θ Θ' x, (∀ i : Fin T, i.val<p+1 → Θ i=Θ' i) → O p (Θ,x)=O p (Θ',x) := by
  intro p Θ Θ' x hh
  by_cases hp : p<T
  · exact hO p hp Θ Θ' x hh
  · have he : Θ=Θ' := funext (fun i => hh i (by have := i.isLt; omega))
    rw [he]

/-- Manuscript logarithmic dimension and integer response-budget
conditions imply the full actual average success bound. The constants
c=c₂/128 and C=128(1+max(log c₁,0))/c₂ are independent of the algorithm,
number of blocks, horizon, response space, and dimension. -/
theorem generalSequential_average_success (ρ : Fin T → Measure H) [∀ i, IsProbabilityMeasure (ρ i)]
    (μ : Measure S) [IsProbabilityMeasure μ] [MeasurableSpace.CountablyGenerated A]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (R : Fin T → Kernel ((Fin T → H) × X) A) [∀ j, IsMarkovKernel (R j)]
    (hO : ∀ p, p<T → ∀ Θ Θ' x, (∀ i : Fin T, i.val<p+1 → Θ i=Θ' i) → O p (Θ,x)=O p (Θ',x))
    (hR : ∀ j Θ Θ' x, (∀ i : Fin T, i.val<j.val → Θ i=Θ' i) → R j (Θ,x)=R j (Θ',x))
    {c₁ c₂ κ D : ℝ} (hc₁ : 0<c₁) (hc₂ : 0<c₂) (hκ : 0<κ)
    (hKL : ∀ j Θ x, klDiv (O j.val (Θ,x)) (R j (Θ,x))≤ENNReal.ofReal κ)
    (N : ℕ) (hT : 0<T)
    (hD : sequentialDimensionConstant c₁ c₂*Real.log (16*(N+1:ℕ)*T)≤D)
    (hcap : 1≤⌊sequentialSmallConstant c₂*D/κ⌋₊)
    (hbudget : N≤T*⌊sequentialSmallConstant c₂*D/κ⌋₊/2)
    (htail : ∀ j x, (ρ j).real {θ | active j θ x}≤c₁*Real.exp (-c₂*D))
    (success : Set (FiniteHistory ((Fin T → H) × S) A N)) (hm : MeasurableSet success)
    (hactive : ∀ h ∈ success, ∀ i, active i ((finiteHistoryInitial N h).1 i)
      (query N (finiteHistoryMapInitial Prod.snd N h))) :
    (adaptiveKernelLaw ((Measure.pi ρ).prod μ) (blockActualKernel active ha query hq O) N).real success≤1/8 := by
  obtain ⟨hδ,hL,hlog,hfast,hfar⟩ := sequential_scalar_conditions hc₁ hc₂ hκ hT hD
  exact blockSequential_average_success ρ μ active ha query hq O R (blockKernel_prefix_of_bounded O hO) hR hκ.le hKL
    ⌊sequentialSmallConstant c₂*D/κ⌋₊ N hT (by omega) (by omega) hδ htail hL hlog hfast hfar success hm hactive

/-- The general sequential response-cost lemma. An arbitrary private
probability space and arbitrary measurable adaptive query/output maps are
fixed first. Under the original logarithmic dimension and half-chain
budget conditions, one deterministic hidden instance has actual success
probability strictly below 1/4. Replies need only be countably generated,
which includes every standard Borel response space. -/
theorem generalSequential_response_cost (ρ : Fin T → Measure H) [∀ i, IsProbabilityMeasure (ρ i)]
    (μ : Measure S) [IsProbabilityMeasure μ] [MeasurableSpace.CountablyGenerated A]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (R : Fin T → Kernel ((Fin T → H) × X) A) [∀ j, IsMarkovKernel (R j)]
    (hO : ∀ p, p<T → ∀ Θ Θ' x, (∀ i : Fin T, i.val<p+1 → Θ i=Θ' i) → O p (Θ,x)=O p (Θ',x))
    (hR : ∀ j Θ Θ' x, (∀ i : Fin T, i.val<j.val → Θ i=Θ' i) → R j (Θ,x)=R j (Θ',x))
    {c₁ c₂ κ D : ℝ} (hc₁ : 0<c₁) (hc₂ : 0<c₂) (hκ : 0<κ)
    (hKL : ∀ j Θ x, klDiv (O j.val (Θ,x)) (R j (Θ,x))≤ENNReal.ofReal κ)
    (N : ℕ) (hT : 0<T)
    (hD : sequentialDimensionConstant c₁ c₂*Real.log (16*(N+1:ℕ)*T)≤D)
    (hcap : 1≤⌊sequentialSmallConstant c₂*D/κ⌋₊)
    (hbudget : N≤T*⌊sequentialSmallConstant c₂*D/κ⌋₊/2)
    (htail : ∀ j x, (ρ j).real {θ | active j θ x}≤c₁*Real.exp (-c₂*D))
    (success : Set ((Fin T → H) × FiniteHistory S A N)) (hm : MeasurableSet success)
    (hactive : ∀ Θ h, (Θ,h) ∈ success → ∀ i, active i (Θ i) (query N h)) :
    ∃ Θ, (adaptiveKernelLaw μ (blockActualFixedKernel active ha query hq O Θ) N).real
      {h | (Θ,h) ∈ success}<(1:ℝ)/4 := by
  apply blockActual_exists_hard_event ρ μ active ha query hq O N hm
  exact generalSequential_average_success ρ μ active ha query hq O R hO hR hc₁ hc₂ hκ hKL N hT hD hcap hbudget htail _
    (hm.preimage (historyHiddenPair_measurable N)) (fun h hh => hactive _ _ hh)

end
end SecondOrder
