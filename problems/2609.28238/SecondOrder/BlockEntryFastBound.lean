import SecondOrder.BlockTargetFastEvent
import SecondOrder.KernelHiddenContinuation

open MeasureTheory ProbabilityTheory InformationTheory
open scoped Classical ENNReal

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSpace S] [MeasurableSpace A]

/-- Every actual first-entry public history is a valid restart for every
possible new hidden target value. This includes stage zero at time zero. -/
theorem blockFirstEntry_good (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) (j : Fin T)
    (n : ℕ) (h : FiniteHistory S A n)
    (hh : h ∈ kernelFirstExitSet (blockPreEntrySet active query Θ j) n) :
    ∀ θ, blockResumedEntryGood active query Θ j n (θ,h) := by
  intro θ
  by_cases hj : j.val=0
  · cases n with
    | zero => exact ⟨by simpa only [hj] using Nat.zero_le 1,by simpa only [hj] using Nat.zero_le 0⟩
    | succ n =>
      have hp := kernelSurvivalSet_subset (blockPreEntrySet active query Θ j) n hh.1
      have hz := hp.1
      omega
  · have hpos : 0<j.val := by omega
    have hp := (blockFirstEntry_index active query Θ j hpos n h hh).2
    have he := blockComparisonProgress_prefix active query Θ (Function.update Θ j θ) n h (fun i hi =>
      (Function.update_of_ne (by intro he; subst i; omega) _ _).symm)
    change j.val≤blockComparisonProgress active query (Function.update Θ j θ) n h+1 ∧
      blockComparisonProgress active query (Function.update Θ j θ) n h≤j.val
    rw [←he]
    omega

/-- Each random-entry slice is bounded by its actual unnormalised public
entry mass. No division by an entry probability, positive-mass assumption,
or extra factor for the number of possible entry times is introduced. -/
theorem blockTarget_firstEntry_fast_bound (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ] [MeasurableSpace.CountablyGenerated A]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (R : Kernel ((Fin T → H) × X) A) [IsMarkovKernel R]
    (hO : ∀ p Θ Θ' x, (∀ i : Fin T, i.val<p+1 → Θ i=Θ' i) → O p (Θ,x)=O p (Θ',x))
    (Θ : Fin T → H) (j : Fin T)
    (hR : ∀ Θ Θ' x, (∀ i : Fin T, i.val<j.val → Θ i=Θ' i) → R (Θ,x)=R (Θ',x))
    {κ : ℝ} (hκ : 0≤κ) (hKL : ∀ Θ x, klDiv (O j.val (Θ,x)) (R (Θ,x))≤ENNReal.ofReal κ)
    (n cap N : ℕ) {δ L : ℝ} (hδ : 0<δ) (htail : ∀ x, ρ.real {θ | active j θ x}≤δ)
    (hL : 0<L) (hlog : L≤Real.log (1/((N+1:ℕ)*δ))) :
    (kernelContinuation (blockTargetKernel active ha query hq O Θ j) n N ∘ₘ
      (adaptiveKernelLaw (ρ.prod μ) (blockTargetKernel active ha query hq O Θ j) n).restrict
        (finiteHistoryMapInitial Prod.snd n ⁻¹' kernelFirstExitSet (blockPreEntrySet active query Θ j) n))
      (blockTargetFastSet active query Θ j cap (n+N))≤
      ENNReal.ofReal (((cap:ℝ)*κ+Real.log 2)/L)*
        adaptiveKernelLaw μ (blockFixedKernel active ha query hq O Θ) n
          (kernelFirstExitSet (blockPreEntrySet active query Θ j) n) := by
  let ν := (adaptiveKernelLaw μ (blockFixedKernel active ha query hq O Θ) n).restrict
    (kernelFirstExitSet (blockPreEntrySet active query Θ j) n)
  have he := blockTarget_firstEntry_independent ρ μ active ha query hq O hO Θ j n
  have hb := kernelHiddenContinuation_bound (blockTargetKernel active ha query hq O Θ j) n N _ ρ ν he
    (blockTargetFastSet_measurable active ha query hq Θ j cap (n+N)) (q := ENNReal.ofReal (((cap:ℝ)*κ+Real.log 2)/L))
  have hf : ∀ᵐ h ∂ν, (∫⁻ θ, kernelContinuation (blockTargetKernel active ha query hq O Θ j) n N
      (historyJoinHidden n (θ,h)) (blockTargetFastSet active query Θ j cap (n+N)) ∂ρ)≤
      ENNReal.ofReal (((cap:ℝ)*κ+Real.log 2)/L) := by
    filter_upwards [ae_restrict_mem (kernelFirstExitSet_measurable _ (blockPreEntrySet_measurable active ha query hq Θ j) n)] with h hh
    exact blockTarget_fastContinuation_bound ρ active ha query hq O R hO Θ j hR hκ hKL n cap h
      (blockFirstEntry_good active query Θ j n h hh)
      (blockStageReferenceKernel active ha (rebasedQuery query n) (rebasedQuery_measurable query hq n) O R Θ j)
      N hδ htail hL hlog
  simpa only [ν,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter] using hb hf

end
end SecondOrder
