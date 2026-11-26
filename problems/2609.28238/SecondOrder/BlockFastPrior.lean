import SecondOrder.BlockTargetFastProbability
import SecondOrder.BlockFarPrior

open MeasureTheory ProbabilityTheory InformationTheory
open scoped Classical ENNReal

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSpace S] [MeasurableSpace A]

def blockFastSlice (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (j : Fin T) (cap N : ℕ) :
    Set ((Fin T → H) × FiniteHistory S A N) :=
  {z | blockStageCharges active query z.1 N z.2 j<cap ∧
    j.val<max (blockComparisonProgress active query z.1 N z.2) (blockComparisonIndex active query z.1 N z.2)}

theorem blockFastSlice_measurable (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (j : Fin T) (cap N : ℕ) : MeasurableSet (blockFastSlice active query j cap N) :=
  (measurableSet_lt (blockStageCharges_measurable active ha query hq j N) measurable_const).inter
    (measurableSet_lt measurable_const ((blockComparisonProgress_measurable active ha query hq N).max
      (blockComparisonIndex_measurable active ha query hq N)))

def blockFastEvent (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (j : Fin T) (cap N : ℕ) :
    Set (FiniteHistory ((Fin T → H) × S) A N) :=
  {h | ((finiteHistoryInitial N h).1,finiteHistoryMapInitial Prod.snd N h) ∈ blockFastSlice active query j cap N}

theorem blockFastEvent_measurable (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (j : Fin T) (cap N : ℕ) : MeasurableSet (blockFastEvent active query j cap N) :=
  (blockFastSlice_measurable active ha query hq j cap N).preimage (historyHiddenPair_measurable N)

/-- The genuine comparison fast-stage event under the complete product
prior. All random entry histories and all other hidden blocks have been
integrated using the original kernels. -/
theorem blockFast_probability (ρ : Fin T → Measure H) [∀ i, IsProbabilityMeasure (ρ i)]
    (μ : Measure S) [IsProbabilityMeasure μ] [MeasurableSpace.CountablyGenerated A]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (R : Kernel ((Fin T → H) × X) A) [IsMarkovKernel R]
    (hO : ∀ p Θ Θ' x, (∀ i : Fin T, i.val<p+1 → Θ i=Θ' i) → O p (Θ,x)=O p (Θ',x))
    (j : Fin T)
    (hR : ∀ Θ Θ' x, (∀ i : Fin T, i.val<j.val → Θ i=Θ' i) → R (Θ,x)=R (Θ',x))
    {κ : ℝ} (hκ : 0≤κ) (hKL : ∀ Θ x, klDiv (O j.val (Θ,x)) (R (Θ,x))≤ENNReal.ofReal κ)
    (cap N : ℕ) {δ L : ℝ} (hδ : 0<δ) (htail : ∀ x, (ρ j).real {θ | active j θ x}≤δ)
    (hL : 0<L) (hlog : L≤Real.log (1/((N+1:ℕ)*δ))) :
    (adaptiveKernelLaw ((Measure.pi ρ).prod μ) (blockComparisonKernel active ha query hq O) N).real
      (blockFastEvent active query j cap N)≤((cap:ℝ)*κ+Real.log 2)/L := by
  let q : ℝ := ((cap:ℝ)*κ+Real.log 2)/L
  have hq₀ : 0≤q := div_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hκ)
    (Real.log_nonneg (by norm_num))) hL.le
  apply ENNReal.toReal_le_of_le_ofReal hq₀
  let E := blockFastSlice active query j cap N
  have hE : MeasurableSet E := blockFastSlice_measurable active ha query hq j cap N
  let F := fun Θ => adaptiveKernelLaw μ (blockFixedKernel active ha query hq O Θ) N {h | (Θ,h) ∈ E}
  have hF : Measurable F := blockFixed_probability_measurable μ active ha query hq O N hE
  change adaptiveKernelLaw ((Measure.pi ρ).prod μ) (blockComparisonKernel active ha query hq O) N
    {h | ((finiteHistoryInitial N h).1,finiteHistoryMapInitial Prod.snd N h) ∈ E}≤ENNReal.ofReal q
  rw [blockComparison_probability_mixture (Measure.pi ρ) μ active ha query hq O N hE]
  change (∫⁻ Θ, F Θ ∂Measure.pi ρ)≤ENNReal.ofReal q
  rw [←lintegral_independent_coordinate_refresh ρ j hF]
  calc
    _ ≤ ∫⁻ _ : Fin T → H, ENNReal.ofReal q ∂Measure.pi ρ := by
      apply lintegral_mono
      intro Θ
      have hm := blockTarget_probability_mixture (ρ j) μ active ha query hq O Θ j N hE
      dsimp only [F]
      apply hm.symm.le.trans
      change adaptiveKernelLaw ((ρ j).prod μ) (blockTargetKernel active ha query hq O Θ j) N
        (blockTargetFastSet active query Θ j cap N)≤ENNReal.ofReal q
      have hb := ENNReal.ofReal_le_ofReal
        (blockTarget_fast_probability (ρ j) μ active ha query hq O R hO Θ j hR hκ hKL cap N hδ htail hL hlog)
      simpa only [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] using hb
    _ = ENNReal.ofReal q := by simp

end
end SecondOrder
