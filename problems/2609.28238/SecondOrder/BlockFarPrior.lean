import SecondOrder.BlockParameterMixture
import SecondOrder.IndependentCoordinateRefresh
import SecondOrder.BlockTargetFarJump
import SecondOrder.BlockComparisonCoupling

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSpace S] [MeasurableSpace A]

def blockFarSlice (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (j : Fin T) (n : ℕ) :
    Set ((Fin T → H) × FiniteHistory S A n) :=
  {z | blockComparisonProgress active query z.1 n z.2<j.val ∧ active j (z.1 j) (query n z.2)}

theorem blockFarSlice_measurable (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n)) (j : Fin T) (n : ℕ) :
    MeasurableSet (blockFarSlice active query j n) := by
  have hm : Measurable (fun z : (Fin T → H) × FiniteHistory S A n => (z.1 j,query n z.2)) :=
    ((measurable_pi_apply j).comp measurable_fst).prodMk ((hq n).comp measurable_snd)
  have hb : MeasurableSet {z : (Fin T → H) × FiniteHistory S A n | active j (z.1 j) (query n z.2)} :=
    (ha j).preimage hm
  exact (measurableSet_lt (blockComparisonProgress_measurable active ha query hq n) measurable_const).inter hb

def blockFarEvent (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (j : Fin T) (n : ℕ) :
    Set (FiniteHistory ((Fin T → H) × S) A n) :=
  {h | ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h) ∈ blockFarSlice active query j n}

theorem blockFarEvent_measurable (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n)) (j : Fin T) (n : ℕ) :
    MeasurableSet (blockFarEvent active query j n) :=
  (blockFarSlice_measurable active ha query hq j n).preimage (historyHiddenPair_measurable n)

/-- Integrating the proved target-block bound over every other hidden block
gives the far-jump bound under the complete independent hidden prior. -/
theorem blockFar_probability (ρ : Fin T → Measure H) [∀ i, IsProbabilityMeasure (ρ i)]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (hO : ∀ p Θ Θ' x, (∀ i : Fin T, i.val<p+1 → Θ i=Θ' i) → O p (Θ,x)=O p (Θ',x))
    (j : Fin T) (n : ℕ) {q : ℝ≥0∞} (htail : ∀ x, ρ j {θ | active j θ x}≤q) :
    adaptiveKernelLaw ((Measure.pi ρ).prod μ) (blockComparisonKernel active ha query hq O) n
      (blockFarEvent active query j n) ≤ q := by
  let E := blockFarSlice active query j n
  have hE : MeasurableSet E := blockFarSlice_measurable active ha query hq j n
  let F := fun Θ => adaptiveKernelLaw μ (blockFixedKernel active ha query hq O Θ) n {h | (Θ,h) ∈ E}
  have hF : Measurable F := blockFixed_probability_measurable μ active ha query hq O n hE
  change adaptiveKernelLaw ((Measure.pi ρ).prod μ) (blockComparisonKernel active ha query hq O) n
    {h | ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h) ∈ E}≤q
  rw [blockComparison_probability_mixture (Measure.pi ρ) μ active ha query hq O n hE]
  change (∫⁻ Θ, F Θ ∂Measure.pi ρ)≤q
  rw [←lintegral_independent_coordinate_refresh ρ j hF]
  calc
    _ ≤ ∫⁻ _ : Fin T → H, q ∂Measure.pi ρ := by
      apply lintegral_mono
      intro Θ
      have hm := blockTarget_probability_mixture (ρ j) μ active ha query hq O Θ j n hE
      have he : {h : FiniteHistory (H × S) A n |
          (Function.update Θ j (finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h) ∈ E} =
          blockTargetFarEvent active query Θ j n := by
        ext h
        simp only [E,blockFarSlice,blockTargetFarEvent,Set.mem_setOf_eq,Function.update_self]
      dsimp only [F]
      exact hm.symm.le.trans (by
        rw [he]
        exact blockTarget_far_probability (ρ j) μ active ha query hq O hO Θ j n htail)
    _ = q := by simp

theorem blockFar_probability_real (ρ : Fin T → Measure H) [∀ i, IsProbabilityMeasure (ρ i)]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (hO : ∀ p Θ Θ' x, (∀ i : Fin T, i.val<p+1 → Θ i=Θ' i) → O p (Θ,x)=O p (Θ',x))
    (j : Fin T) (n : ℕ) {q : ℝ} (hq₀ : 0≤q) (htail : ∀ x, (ρ j).real {θ | active j θ x}≤q) :
    (adaptiveKernelLaw ((Measure.pi ρ).prod μ) (blockComparisonKernel active ha query hq O) n).real
      (blockFarEvent active query j n) ≤ q := by
  apply ENNReal.toReal_le_of_le_ofReal hq₀
  apply blockFar_probability ρ μ active ha query hq O hO j n
  intro x
  rw [←ENNReal.ofReal_toReal (measure_ne_top (ρ j) {θ | active j θ x})]
  exact ENNReal.ofReal_le_ofReal (htail x)

theorem blockNoFarSet_compl (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (n : ℕ) :
    (blockNoFarSet active query n)ᶜ=⋃ j, blockFarEvent active query j n := by
  ext h
  simp only [blockNoFarSet,blockFarEvent,blockFarSlice,blockHistoryProgress,Set.mem_compl_iff,
    Set.mem_setOf_eq,Set.mem_iUnion,not_forall,Classical.not_imp,not_not,Nat.lt_iff_add_one_le,exists_prop]

end
end SecondOrder
