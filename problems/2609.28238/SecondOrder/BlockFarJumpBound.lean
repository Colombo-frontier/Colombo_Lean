import SecondOrder.BlockFarPrior
import SecondOrder.KernelSurvivalUnion

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSpace S] [MeasurableSpace A]

theorem blockNoFar_failure_probability (ρ : Fin T → Measure H) [∀ i, IsProbabilityMeasure (ρ i)]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (hO : ∀ p Θ Θ' x, (∀ i : Fin T, i.val<p+1 → Θ i=Θ' i) → O p (Θ,x)=O p (Θ',x))
    (n : ℕ) {δ : ℝ} (hδ : 0≤δ) (htail : ∀ i x, (ρ i).real {θ | active i θ x}≤δ) :
    (adaptiveKernelLaw ((Measure.pi ρ).prod μ) (blockComparisonKernel active ha query hq O) n).real
      (blockNoFarSet active query n)ᶜ ≤ (T:ℝ)*δ := by
  rw [blockNoFarSet_compl]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ _j : Fin T, δ := Finset.sum_le_sum (fun j _ =>
      blockFar_probability_real ρ μ active ha query hq O hO j n hδ (htail j))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

/-- Full-horizon far-jump bound under the complete independent hidden
prior, including the terminal unqueried output: `(N+1) T δ`. -/
theorem blockFarJump_probability (ρ : Fin T → Measure H) [∀ i, IsProbabilityMeasure (ρ i)]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (hO : ∀ p Θ Θ' x, (∀ i : Fin T, i.val<p+1 → Θ i=Θ' i) → O p (Θ,x)=O p (Θ',x))
    (N : ℕ) {δ : ℝ} (hδ : 0≤δ) (htail : ∀ i x, (ρ i).real {θ | active i θ x}≤δ) :
    (adaptiveKernelLaw ((Measure.pi ρ).prod μ) (blockComparisonKernel active ha query hq O) N).real
      (kernelSurvivalSet (blockNoFarSet active query) N)ᶜ ≤ (N+1:ℕ)*T*δ := by
  have hh := adaptiveKernelLaw_exit_uniform ((Measure.pi ρ).prod μ)
    (blockComparisonKernel active ha query hq O) (blockNoFarSet active query)
    (blockNoFarSet_measurable active ha query hq) N
    (fun n _ => blockNoFar_failure_probability ρ μ active ha query hq O hO n hδ htail)
  simpa only [mul_assoc] using hh

/-- The actual success probability is reduced to comparison completion
with the manuscript's complete far-jump error already proved. -/
theorem blockActual_success_le_completion (ρ : Fin T → Measure H) [∀ i, IsProbabilityMeasure (ρ i)]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (hO : ∀ p Θ Θ' x, (∀ i : Fin T, i.val<p+1 → Θ i=Θ' i) → O p (Θ,x)=O p (Θ',x))
    (N : ℕ) {δ : ℝ} (hδ : 0≤δ) (htail : ∀ i x, (ρ i).real {θ | active i θ x}≤δ)
    (success : Set (FiniteHistory ((Fin T → H) × S) A N)) (hm : MeasurableSet success)
    (hactive : ∀ h ∈ success, ∀ i, active i ((finiteHistoryInitial N h).1 i)
      (query N (finiteHistoryMapInitial Prod.snd N h))) :
    (adaptiveKernelLaw ((Measure.pi ρ).prod μ) (blockActualKernel active ha query hq O) N).real success ≤
      (adaptiveKernelLaw ((Measure.pi ρ).prod μ) (blockComparisonKernel active ha query hq O) N).real
        {h | blockHistoryFinish active query N h=T}+(N+1:ℕ)*T*δ :=
  (blockActual_success_le_comparison ((Measure.pi ρ).prod μ) active ha query hq O N success hm hactive).trans
    (add_le_add_left (blockFarJump_probability ρ μ active ha query hq O hO N hδ htail) _)

end
end SecondOrder
