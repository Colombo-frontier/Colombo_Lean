import SecondOrder.BlockResumedProbability
import SecondOrder.ResumedHiddenLaw
import SecondOrder.AdaptiveKernelInitial

open MeasureTheory ProbabilityTheory InformationTheory
open scoped Classical ENNReal

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSpace S] [MeasurableSpace A]

def blockTargetFastSet (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) (j : Fin T) (cap N : ℕ) :
    Set (FiniteHistory (H × S) A N) :=
  {h | blockStageCharges active query (Function.update Θ j (finiteHistoryInitial N h).1)
      N (finiteHistoryMapInitial Prod.snd N h) j<cap ∧
    j.val<max (blockComparisonProgress active query (Function.update Θ j (finiteHistoryInitial N h).1)
      N (finiteHistoryMapInitial Prod.snd N h))
      (blockComparisonIndex active query (Function.update Θ j (finiteHistoryInitial N h).1)
      N (finiteHistoryMapInitial Prod.snd N h))}

theorem blockTargetFastSet_measurable (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (Θ : Fin T → H) (j : Fin T) (cap N : ℕ) : MeasurableSet (blockTargetFastSet active query Θ j cap N) := by
  have hm : Measurable (fun h : FiniteHistory (H × S) A N =>
      (Function.update Θ j (finiteHistoryInitial N h).1,finiteHistoryMapInitial Prod.snd N h)) :=
    ((measurable_update Θ).comp (measurable_fst.comp (finiteHistoryInitial_measurable N))).prodMk
      (finiteHistoryMapInitial_measurable measurable_snd N)
  exact (measurableSet_lt ((blockStageCharges_measurable active ha query hq j N).comp hm) measurable_const).inter
    (measurableSet_lt measurable_const (((blockComparisonProgress_measurable active ha query hq N).comp hm).max
      ((blockComparisonIndex_measurable active ha query hq N).comp hm)))

theorem blockResumedEntryGood_measurable (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (Θ : Fin T → H) (j : Fin T) (n : ℕ) : MeasurableSet {h | blockResumedEntryGood active query Θ j n h} := by
  have hm : Measurable (fun h : H × FiniteHistory S A n =>
      blockComparisonProgress active query (Function.update Θ j h.1) n h.2) :=
    (blockComparisonProgress_measurable active ha query hq n).comp
      (((measurable_update Θ).comp measurable_fst).prodMk measurable_snd)
  exact (measurableSet_le measurable_const (hm.add_const 1)).inter (measurableSet_le hm measurable_const)

/-- Fast completion in the original histories, after restarting from a
valid entry law, is covered almost surely by the transferred activation. -/
theorem blockResumed_fast_probability_le_stopped (ρ : Measure H) [IsProbabilityMeasure ρ]
    (n : ℕ) (μ : Measure (FiniteHistory S A n)) [IsProbabilityMeasure μ]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (Θ : Fin T → H) (j : Fin T) (cap N : ℕ)
    (hg : ∀ᵐ h ∂ρ.prod μ, blockResumedEntryGood active query Θ j n h) :
    (adaptiveKernelLaw (ρ.prod μ) (resumedHiddenKernel (blockTargetKernel active ha query hq O Θ j) n) N).real
      (historyResumeHidden n N ⁻¹' blockTargetFastSet active query Θ j cap (n+N))≤
    (adaptiveKernelLaw (ρ.prod μ) (resumedHiddenKernel (blockTargetKernel active ha query hq O Θ j) n) N).real
      (kernelStoppedHitSet (blockResumedSafe active query Θ j n cap) (blockResumedActive active query j n) N) := by
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [adaptiveKernelLaw_initial_ae (ρ.prod μ)
    (resumedHiddenKernel (blockTargetKernel active ha query hq O Θ j) n) hg N] with h hh
  intro hf
  change historyResumeHidden n N h ∈ blockTargetFastSet active query Θ j cap (n+N) at hf
  simp only [blockTargetFastSet,Set.mem_setOf_eq,historyResumeHidden_initial,historyResumeHidden_public] at hf
  exact blockResumed_fastCompletion_subset active query Θ j n cap N h hh hf.1 hf.2

theorem blockTarget_fastContinuation_bound (ρ : Measure H) [IsProbabilityMeasure ρ]
    [MeasurableSpace.CountablyGenerated A]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (R : Kernel ((Fin T → H) × X) A) [IsMarkovKernel R]
    (hO : ∀ p Θ Θ' x, (∀ i : Fin T, i.val<p+1 → Θ i=Θ' i) → O p (Θ,x)=O p (Θ',x))
    (Θ : Fin T → H) (j : Fin T)
    (hR : ∀ Θ Θ' x, (∀ i : Fin T, i.val<j.val → Θ i=Θ' i) → R (Θ,x)=R (Θ',x))
    {κ : ℝ} (hκ : 0≤κ) (hKL : ∀ Θ x, klDiv (O j.val (Θ,x)) (R (Θ,x))≤ENNReal.ofReal κ)
    (n cap : ℕ) (h₀ : FiniteHistory S A n)
    (hg : ∀ θ, blockResumedEntryGood active query Θ j n (θ,h₀))
    (dummy : ∀ k, Kernel (FiniteHistory (FiniteHistory S A n) A k) A) [∀ k, IsMarkovKernel (dummy k)]
    (N : ℕ) {δ L : ℝ} (hδ : 0<δ) (htail : ∀ x, ρ.real {θ | active j θ x}≤δ)
    (hL : 0<L) (hlog : L≤Real.log (1/((N+1:ℕ)*δ))) :
    (∫⁻ θ, kernelContinuation (blockTargetKernel active ha query hq O Θ j) n N
      (historyJoinHidden n (θ,h₀)) (blockTargetFastSet active query Θ j cap (n+N)) ∂ρ)≤
      ENNReal.ofReal (((cap:ℝ)*κ+Real.log 2)/L) := by
  have hgood : ∀ᵐ h ∂ρ.prod (Measure.dirac h₀), blockResumedEntryGood active query Θ j n h := by
    apply (Measure.ae_prod_iff_ae_ae (blockResumedEntryGood_measurable active ha query hq Θ j n)).mpr
    exact Filter.Eventually.of_forall (fun θ =>
      (ae_dirac_iff ((blockResumedEntryGood_measurable active ha query hq Θ j n).preimage measurable_prodMk_left)).mpr (hg θ))
  have hb := (blockResumed_fast_probability_le_stopped ρ n (Measure.dirac h₀) active ha query hq O Θ j cap N hgood).trans
    (blockResumed_stoppedHit_bound ρ n (Measure.dirac h₀) active ha query hq O R hO Θ j hR hκ hKL cap dummy N hδ htail hL hlog)
  rw [←resumedHiddenLaw_prior_event (blockTargetKernel active ha query hq O Θ j) ρ n h₀ N
    (blockTargetFastSet_measurable active ha query hq Θ j cap (n+N))]
  have he := ENNReal.ofReal_le_ofReal hb
  simpa only [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] using he

end
end SecondOrder
