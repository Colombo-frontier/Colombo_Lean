import SecondOrder.BlockStageKernels

open MeasureTheory ProbabilityTheory InformationTheory
open scoped Classical ENNReal

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSpace S] [MeasurableSpace A]

/-- The actual capped continuation driven by the block extensions. -/
def blockStageLaw (ρ : Measure H) (μ : Measure S)
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) (Θ : Fin T → H) (j : Fin T)
    (cap : ℕ) (dummy : ∀ n, Kernel (FiniteHistory S A n) A) (N : ℕ) :
    Measure (FiniteHistory (H × S) A N) :=
  kernelStageTrueLaw ρ μ (blockStageSelected active query Θ j)
    (blockStageSelected_measurable active ha query hq Θ j) cap
    (blockStageTrueKernel active ha query hq O Θ j) dummy N

/-- Prefix dependence and the one-step information bound imply the
activation bound for this concrete block continuation. `observed` includes
any measurable queries and the terminal output read from the final history. -/
theorem blockStage_activation_bound (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ] [MeasurableSpace.CountablyGenerated A]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (R : Kernel ((Fin T → H) × X) A) [IsMarkovKernel R]
    (hO : ∀ p Θ Θ' x, (∀ i : Fin T, i.val<p+1 → Θ i=Θ' i) → O p (Θ,x)=O p (Θ',x))
    (Θ : Fin T → H) (j : Fin T)
    (hR : ∀ Θ Θ' x, (∀ i : Fin T, i.val<j.val → Θ i=Θ' i) → R (Θ,x)=R (Θ',x))
    {κ : ℝ} (hκ : 0≤κ) (hKL : ∀ Θ x, klDiv (O j.val (Θ,x)) (R (Θ,x))≤ENNReal.ofReal κ)
    (cap : ℕ) (dummy : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (dummy n)]
    (N : ℕ) (observed : Fin (N+1) → FiniteHistory S A N → X)
    (hm : ∀ t, Measurable (observed t)) {δ L : ℝ} (hδ : 0<δ)
    (htail : ∀ x, ρ.real {θ | active j θ x}≤δ)
    (hL : 0<L) (hlog : L≤Real.log (1/((N+1:ℕ)*δ))) :
    (blockStageLaw ρ μ active ha query hq O Θ j cap dummy N).real
      {h | ∃ t, active j (finiteHistoryInitial N h).1 (observed t (finiteHistoryMapInitial Prod.snd N h))} ≤
      ((cap:ℝ)*κ+Real.log 2)/L := by
  exact kernelStage_activation_bound ρ μ (blockStageSelected active query Θ j)
    (blockStageSelected_measurable active ha query hq Θ j) cap
    (blockStageTrueKernel active ha query hq O Θ j)
    (blockStageReferenceKernel active ha query hq O R Θ j) dummy hκ
    (blockStageKernels_kl active ha query hq O R hO Θ j hR hKL)
    (blockStageKernels_same_unselected active ha query hq O R hO Θ j)
    N (fun t θ h => active j θ (observed t h))
    (fun t => (ha j).preimage (measurable_fst.prodMk ((hm t).comp measurable_snd)))
    hδ (fun t h => htail (observed t h)) hL hlog

end
end SecondOrder
