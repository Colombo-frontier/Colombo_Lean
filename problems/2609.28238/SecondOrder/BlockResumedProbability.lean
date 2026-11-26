import SecondOrder.BlockResumedFastEvent

open MeasureTheory ProbabilityTheory InformationTheory
open scoped Classical ENNReal

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSpace S] [MeasurableSpace A]

/-- An activation reached before a competing cap/progress stop in the
actual resumed comparison inherits the concrete capped-stage bound. -/
theorem blockResumed_stoppedHit_bound (ρ : Measure H) [IsProbabilityMeasure ρ]
    (n : ℕ) (μ : Measure (FiniteHistory S A n)) [IsProbabilityMeasure μ]
    [MeasurableSpace.CountablyGenerated A]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (R : Kernel ((Fin T → H) × X) A) [IsMarkovKernel R]
    (hO : ∀ p Θ Θ' x, (∀ i : Fin T, i.val<p+1 → Θ i=Θ' i) → O p (Θ,x)=O p (Θ',x))
    (Θ : Fin T → H) (j : Fin T)
    (hR : ∀ Θ Θ' x, (∀ i : Fin T, i.val<j.val → Θ i=Θ' i) → R (Θ,x)=R (Θ',x))
    {κ : ℝ} (hκ : 0≤κ) (hKL : ∀ Θ x, klDiv (O j.val (Θ,x)) (R (Θ,x))≤ENNReal.ofReal κ)
    (cap : ℕ) (dummy : ∀ k, Kernel (FiniteHistory (FiniteHistory S A n) A k) A)
    [∀ k, IsMarkovKernel (dummy k)] (N : ℕ) {δ L : ℝ} (hδ : 0<δ)
    (htail : ∀ x, ρ.real {θ | active j θ x}≤δ)
    (hL : 0<L) (hlog : L≤Real.log (1/((N+1:ℕ)*δ))) :
    (adaptiveKernelLaw (ρ.prod μ) (resumedHiddenKernel (blockTargetKernel active ha query hq O Θ j) n) N).real
      (kernelStoppedHitSet (blockResumedSafe active query Θ j n cap) (blockResumedActive active query j n) N)≤
      ((cap:ℝ)*κ+Real.log 2)/L := by
  let sel := blockStageSelected active (rebasedQuery query n) Θ j
  let hs := blockStageSelected_measurable active ha (rebasedQuery query n) (rebasedQuery_measurable query hq n) Θ j
  let K := blockStageTrueKernel active ha (rebasedQuery query n) (rebasedQuery_measurable query hq n) O Θ j
  let Q := blockStageReferenceKernel active ha (rebasedQuery query n) (rebasedQuery_measurable query hq n) O R Θ j
  have hc := kernelStoppedHit_probability_le (ρ.prod μ)
    (resumedHiddenKernel (blockTargetKernel active ha query hq O Θ j) n)
    (cappedResponseKernel (stageSelected sel) (stageSelected_measurable sel hs) cap K (hiddenIndependentKernel dummy))
    (blockResumedSafe active query Θ j n cap) (blockResumedActive active query j n)
    (blockResumedSafe_measurable active ha query hq Θ j n cap)
    (blockResumedActive_measurable active ha query hq j n)
    (fun _ => Set.disjoint_left.mpr (fun _ hh hh' => hh'.2.2.1 hh))
    (blockResumedKernel_eq_stage active ha query hq O Θ j n cap dummy) N
  apply hc.trans
  exact kernelStage_firstActivation_bound ρ μ sel hs cap K Q dummy hκ
    (blockStageKernels_kl active ha (rebasedQuery query n) (rebasedQuery_measurable query hq n) O R hO Θ j hR hKL)
    (blockStageKernels_same_unselected active ha (rebasedQuery query n) (rebasedQuery_measurable query hq n) O R hO Θ j)
    (fun k θ h => active j θ (rebasedQuery query n k h))
    (fun k => (ha j).preimage (measurable_fst.prodMk ((rebasedQuery_measurable query hq n k).comp measurable_snd)))
    hδ (fun k h => htail (rebasedQuery query n k h)) N hL hlog

end
end SecondOrder
