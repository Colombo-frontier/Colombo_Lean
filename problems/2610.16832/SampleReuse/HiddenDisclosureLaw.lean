import SampleReuse.PersistentHiddenStage
import SampleReuse.PersistentTableKernel

open MeasureTheory ProbabilityTheory SecondOrder
open scoped Classical ENNReal

namespace SampleReuse
noncomputable section

variable {H S A Key : Type} [Fintype H] [Fintype A] [Countable Key]
  [MeasurableSpace H] [MeasurableSingletonClass H] [MeasurableSpace S]
  [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace Key] [MeasurableSingletonClass Key]

set_option maxHeartbeats 400000 in
/-- The hidden parameter is sampled once, while the private seed has an
arbitrary measurable law. Conditional on that parameter, this is exactly the
ordinary persistent disclosure experiment. -/
theorem hiddenDisclosure_lintegral
    (ρ : Measure H) [IsProbabilityMeasure ρ] (μ : Measure S) [IsProbabilityMeasure μ]
    (query : ∀ n, FiniteHistory S A n → Key) (hq : ∀ n, Measurable (query n))
    (p : H → Key → PMF A) :
    ∀ n (F : H × FiniteHistory S A n → ℝ≥0∞), Measurable F →
      (∫⁻ h, F ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)
        ∂adaptiveKernelLaw (ρ.prod μ) (hiddenDisclosureKernel query hq p) n) =
      ∫⁻ θ, ∫⁻ h, F (θ,h)
        ∂adaptiveKernelLaw μ (measurableDisclosureKernel query hq (p θ)) n ∂ρ := by
  intro n
  induction n with
  | zero =>
    intro F hF
    exact lintegral_prod _ hF.aemeasurable
  | succ n ih =>
    intro F hF
    let G : H × FiniteHistory S A n → ℝ≥0∞ := fun z =>
      ∫⁻ a, F (z.1,(z.2,a)) ∂measurableDisclosureKernel query hq (p z.1) n z.2
    have hG : Measurable G := by
      have hh : Measurable (fun z : FiniteHistory S A n × H => G (z.2,z.1)) := by
        apply measurable_from_prod_countable
        intro θ
        exact Measurable.lintegral_kernel_prod_right
          (κ := measurableDisclosureKernel query hq (p θ) n)
          (hF.comp (measurable_const.prodMk measurable_id))
      have hcomp := hh.comp (measurable_swap : Measurable
        (Prod.swap : H × FiniteHistory S A n → FiniteHistory S A n × H))
      have he : ((fun z : FiniteHistory S A n × H => G (z.2,z.1)) ∘ Prod.swap) = G := by
        funext z
        rcases z with ⟨θ,h⟩
        rfl
      rw [he] at hcomp
      exact hcomp
    change (∫⁻ h, F ((finiteHistoryInitial n h.1).1,
      (finiteHistoryMapInitial Prod.snd n h.1,h.2))
      ∂(adaptiveKernelLaw (ρ.prod μ) (hiddenDisclosureKernel query hq p) n ⊗ₘ
        hiddenDisclosureKernel query hq p n)) = _
    rw [Measure.lintegral_compProd]
    · change (∫⁻ h, G ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)
        ∂adaptiveKernelLaw (ρ.prod μ) (hiddenDisclosureKernel query hq p) n) = _
      rw [ih G hG]
      apply lintegral_congr_ae
      filter_upwards [] with θ
      exact (Measure.lintegral_compProd
        (μ := adaptiveKernelLaw μ (measurableDisclosureKernel query hq (p θ)) n)
        (κ := measurableDisclosureKernel query hq (p θ) n)
        (hF.comp (measurable_const.prodMk measurable_id))).symm
    · exact hF.comp ((measurable_fst.comp (finiteHistoryInitial_measurable n)).comp measurable_fst |>.prodMk
        (((finiteHistoryMapInitial_measurable measurable_snd n).comp measurable_fst).prodMk measurable_snd))

def conditionalDisclosureHistoryKernel (μ : Measure S) [IsProbabilityMeasure μ]
    (query : ∀ n, FiniteHistory S A n → Key) (hq : ∀ n, Measurable (query n))
    (p : H → Key → PMF A) (n : ℕ) : Kernel H (FiniteHistory S A n) where
  toFun θ := adaptiveKernelLaw μ (measurableDisclosureKernel query hq (p θ)) n
  measurable' := measurable_of_countable _

instance conditionalDisclosureHistoryKernel_markov (μ : Measure S) [IsProbabilityMeasure μ]
    (query : ∀ n, FiniteHistory S A n → Key) (hq : ∀ n, Measurable (query n))
    (p : H → Key → PMF A) (n : ℕ) :
    IsMarkovKernel (conditionalDisclosureHistoryKernel μ query hq p n) where
  isProbabilityMeasure θ := by
    change IsProbabilityMeasure (adaptiveKernelLaw μ (measurableDisclosureKernel query hq (p θ)) n)
    infer_instance

theorem hiddenDisclosure_split_law
    (ρ : Measure H) [IsProbabilityMeasure ρ] (μ : Measure S) [IsProbabilityMeasure μ]
    (query : ∀ n, FiniteHistory S A n → Key) (hq : ∀ n, Measurable (query n))
    (p : H → Key → PMF A) (n : ℕ) :
    (adaptiveKernelLaw (ρ.prod μ) (hiddenDisclosureKernel query hq p) n).map
      (fun h => ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)) =
      ρ ⊗ₘ conditionalDisclosureHistoryKernel μ query hq p n := by
  ext E hE
  rw [Measure.map_apply (historyHiddenPair_measurable n) hE,
    ← lintegral_indicator_one (hE.preimage (historyHiddenPair_measurable n)),
    ← lintegral_indicator_one hE]
  change (∫⁻ h, E.indicator (fun _ => 1)
      ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)
      ∂adaptiveKernelLaw (ρ.prod μ) (hiddenDisclosureKernel query hq p) n) =
    ∫⁻ z, E.indicator (fun _ => 1) z ∂ρ ⊗ₘ conditionalDisclosureHistoryKernel μ query hq p n
  rw [Measure.lintegral_compProd (measurable_const.indicator hE)]
  exact hiddenDisclosure_lintegral ρ μ query hq p n (E.indicator (fun _ => 1))
    (measurable_const.indicator hE)

theorem hiddenDisclosure_event
    (ρ : Measure H) [IsProbabilityMeasure ρ] (μ : Measure S) [IsProbabilityMeasure μ]
    (query : ∀ n, FiniteHistory S A n → Key) (hq : ∀ n, Measurable (query n))
    (p : H → Key → PMF A) (n : ℕ) (E : H → FiniteHistory S A n → Prop)
    (hE : MeasurableSet {z : H × FiniteHistory S A n | E z.1 z.2}) :
    adaptiveKernelLaw (ρ.prod μ) (hiddenDisclosureKernel query hq p) n
      {h | E (finiteHistoryInitial n h).1 (finiteHistoryMapInitial Prod.snd n h)} =
      ∫⁻ θ, adaptiveKernelLaw μ (measurableDisclosureKernel query hq (p θ)) n
        {h | E θ h} ∂ρ := by
  have hm : MeasurableSet {h : FiniteHistory (H × S) A n |
      E (finiteHistoryInitial n h).1 (finiteHistoryMapInitial Prod.snd n h)} :=
    hE.preimage (historyHiddenPair_measurable n)
  rw [← lintegral_indicator_one hm]
  change (∫⁻ h, {z : H × FiniteHistory S A n | E z.1 z.2}.indicator (fun _ => 1)
    ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)
    ∂adaptiveKernelLaw (ρ.prod μ) (hiddenDisclosureKernel query hq p) n) = _
  rw [hiddenDisclosure_lintegral ρ μ query hq p n _ (measurable_const.indicator hE)]
  apply lintegral_congr_ae
  filter_upwards [] with θ
  exact lintegral_indicator_one (hE.preimage measurable_prodMk_left)

theorem hiddenDisclosure_integral
    (ρ : Measure H) [IsProbabilityMeasure ρ] (μ : Measure S) [IsProbabilityMeasure μ]
    (query : ∀ n, FiniteHistory S A n → Key) (hq : ∀ n, Measurable (query n))
    (p : H → Key → PMF A) (n : ℕ) (F : H × FiniteHistory S A n → ℝ)
    (hF : Measurable F) (M : ℝ) (hb : ∀ z, ‖F z‖ ≤ M) :
    (∫ h, F ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)
      ∂adaptiveKernelLaw (ρ.prod μ) (hiddenDisclosureKernel query hq p) n) =
      ∫ θ, ∫ h, F (θ,h)
        ∂adaptiveKernelLaw μ (measurableDisclosureKernel query hq (p θ)) n ∂ρ := by
  have hi : Integrable F (ρ ⊗ₘ conditionalDisclosureHistoryKernel μ query hq p n) :=
    (integrable_const M).mono' hF.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  rw [← integral_map (historyHiddenPair_measurable n).aemeasurable hF.aestronglyMeasurable,
    hiddenDisclosure_split_law ρ μ query hq p n,Measure.integral_compProd hi]
  rfl

/-- Exact agreement with a once-sampled immutable table, including an
arbitrary measurable private seed and a hidden-dependent sample law. -/
theorem hiddenDisclosure_fixed_table_lintegral [Fintype Key]
    (ρ : Measure H) [IsProbabilityMeasure ρ] (μ : Measure S) [IsProbabilityMeasure μ]
    (query : ∀ n, FiniteHistory S A n → Key) (hq : ∀ n, Measurable (query n))
    (p : H → Key → PMF A) (n : ℕ) (F : H × FiniteHistory S A n → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ h, F ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)
      ∂adaptiveKernelLaw (ρ.prod μ) (hiddenDisclosureKernel query hq p) n) =
      ∫⁻ θ, ∫⁻ z : S × (Key → A), F (θ,tableHistory query z.1 z.2 n)
        ∂μ.prod (finitePiPMF (p θ)).toMeasure ∂ρ := by
  rw [hiddenDisclosure_lintegral ρ μ query hq p n F hF]
  apply lintegral_congr_ae
  filter_upwards [] with θ
  rw [← fixed_table_transcript_law query hq (p θ) μ n]
  exact lintegral_map' (hF.comp measurable_prodMk_left).aemeasurable
    (tableHistory_measurable query hq n).aemeasurable

end
end SampleReuse
