import SecondOrder.BlockFastPrior
import SecondOrder.BlockFarJumpBound
import SecondOrder.MeasureStageCounting

open MeasureTheory ProbabilityTheory InformationTheory
open scoped Classical ENNReal BigOperators

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSpace S] [MeasurableSpace A]

theorem blockComparison_completion_bound (ρ : Fin T → Measure H) [∀ i, IsProbabilityMeasure (ρ i)]
    (μ : Measure S) [IsProbabilityMeasure μ] [MeasurableSpace.CountablyGenerated A]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (R : Fin T → Kernel ((Fin T → H) × X) A) [∀ j, IsMarkovKernel (R j)]
    (hO : ∀ p Θ Θ' x, (∀ i : Fin T, i.val<p+1 → Θ i=Θ' i) → O p (Θ,x)=O p (Θ',x))
    (hR : ∀ j Θ Θ' x, (∀ i : Fin T, i.val<j.val → Θ i=Θ' i) → R j (Θ,x)=R j (Θ',x))
    {κ : ℝ} (hκ : 0≤κ) (hKL : ∀ j Θ x, klDiv (O j.val (Θ,x)) (R j (Θ,x))≤ENNReal.ofReal κ)
    (cap N : ℕ) (hT : 0<T) (hcap : 0<cap) (hbudget : 2*N≤T*cap)
    {δ L : ℝ} (hδ : 0<δ) (htail : ∀ j x, (ρ j).real {θ | active j θ x}≤δ)
    (hL : 0<L) (hlog : L≤Real.log (1/((N+1:ℕ)*δ)))
    (hfast : ((cap:ℝ)*κ+Real.log 2)/L≤1/32) :
    (adaptiveKernelLaw ((Measure.pi ρ).prod μ) (blockComparisonKernel active ha query hq O) N).real
      {h | blockHistoryFinish active query N h=T}≤1/16 := by
  let cost : Fin T → FiniteHistory ((Fin T → H) × S) A N → ℕ := fun j h =>
    blockStageCharges active query (finiteHistoryInitial N h).1 N (finiteHistoryMapInitial Prod.snd N h) j
  let reached : Fin T → Set (FiniteHistory ((Fin T → H) × S) A N) :=
    fun j => {h | j.val<blockHistoryFinish active query N h}
  have he (j : Fin T) : {h | h ∈ reached j ∧ cost j h<cap}=blockFastEvent active query j cap N := by
    ext h
    exact and_comm
  apply measure_sequential_completion_probability _ hT hcap cost reached _
    ((blockHistoryFinish_measurable active ha query hq N) (measurableSet_singleton T))
  · intro j
    rw [he]
    exact blockFastEvent_measurable active ha query hq j cap N
  · intro h hh j
    change j.val<blockHistoryFinish active query N h
    rw [show blockHistoryFinish active query N h=T from hh]
    exact j.isLt
  · intro h
    exact sum_blockStageCharges_le active query (finiteHistoryInitial N h).1 N (finiteHistoryMapInitial Prod.snd N h)
  · exact hbudget
  · intro j
    rw [he]
    exact (blockFast_probability ρ μ active ha query hq O (R j) hO j (hR j) hκ (hKL j) cap N hδ (htail j) hL hlog).trans hfast

/-- The general sequential comparison for arbitrary countably generated
reply spaces, with all entry, independence, truncation and charging claims
derived from the actual kernels. Only scalar numerical budget conditions
remain in this quantitative form. -/
theorem blockSequential_average_success (ρ : Fin T → Measure H) [∀ i, IsProbabilityMeasure (ρ i)]
    (μ : Measure S) [IsProbabilityMeasure μ] [MeasurableSpace.CountablyGenerated A]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (R : Fin T → Kernel ((Fin T → H) × X) A) [∀ j, IsMarkovKernel (R j)]
    (hO : ∀ p Θ Θ' x, (∀ i : Fin T, i.val<p+1 → Θ i=Θ' i) → O p (Θ,x)=O p (Θ',x))
    (hR : ∀ j Θ Θ' x, (∀ i : Fin T, i.val<j.val → Θ i=Θ' i) → R j (Θ,x)=R j (Θ',x))
    {κ : ℝ} (hκ : 0≤κ) (hKL : ∀ j Θ x, klDiv (O j.val (Θ,x)) (R j (Θ,x))≤ENNReal.ofReal κ)
    (cap N : ℕ) (hT : 0<T) (hcap : 0<cap) (hbudget : 2*N≤T*cap)
    {δ L : ℝ} (hδ : 0<δ) (htail : ∀ j x, (ρ j).real {θ | active j θ x}≤δ)
    (hL : 0<L) (hlog : L≤Real.log (1/((N+1:ℕ)*δ)))
    (hfast : ((cap:ℝ)*κ+Real.log 2)/L≤1/32) (hfar : (N+1:ℕ)*T*δ≤1/16)
    (success : Set (FiniteHistory ((Fin T → H) × S) A N)) (hm : MeasurableSet success)
    (hactive : ∀ h ∈ success, ∀ i, active i ((finiteHistoryInitial N h).1 i)
      (query N (finiteHistoryMapInitial Prod.snd N h))) :
    (adaptiveKernelLaw ((Measure.pi ρ).prod μ) (blockActualKernel active ha query hq O) N).real success≤1/8 := by
  have hc := blockComparison_completion_bound ρ μ active ha query hq O R hO hR hκ hKL cap N hT hcap hbudget hδ htail hL hlog hfast
  have hs := blockActual_success_le_completion ρ μ active ha query hq O hO N hδ.le htail success hm hactive
  linarith

end
end SecondOrder
