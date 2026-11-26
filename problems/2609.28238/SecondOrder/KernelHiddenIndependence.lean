import SecondOrder.AdaptiveKernelLaw
import SecondOrder.FiniteReferenceIndependence

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

universe u
namespace SecondOrder
noncomputable section
variable {H S U A : Type u} [MeasurableSpace H] [MeasurableSpace S]
  [MeasurableSpace U] [MeasurableSpace A]

theorem finiteHistoryInitial_measurable : ∀ n, Measurable (finiteHistoryInitial (S := S) (A := A) n) := by
  intro n
  induction n with
  | zero => exact measurable_id
  | succ n ih => exact ih.comp measurable_fst

theorem finiteHistoryMapInitial_measurable {f : S → U} (hf : Measurable f) :
    ∀ n, Measurable (finiteHistoryMapInitial (A := A) f n) := by
  intro n
  induction n with
  | zero => exact hf
  | succ n ih => exact (ih.comp measurable_fst).prodMk measurable_snd

theorem historyHiddenPair_measurable (n : ℕ) : Measurable
    (fun h : FiniteHistory (H × S) A n => ((finiteHistoryInitial n h).1,
      finiteHistoryMapInitial Prod.snd n h)) :=
  (measurable_fst.comp (finiteHistoryInitial_measurable n)).prodMk
    (finiteHistoryMapInitial_measurable measurable_snd n)

/-- The reference kernel observes the public history and cannot inspect
the first component of the initial state. -/
def hiddenIndependentKernel (Q : ∀ n, Kernel (FiniteHistory S A n) A) (n : ℕ) :
    Kernel (FiniteHistory (H × S) A n) A :=
  (Q n).comap (finiteHistoryMapInitial Prod.snd n)
    (finiteHistoryMapInitial_measurable measurable_snd n)

instance hiddenIndependentKernel_markov (Q : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (Q n)] (n : ℕ) :
    IsMarkovKernel (hiddenIndependentKernel (H := H) Q n) := by
  unfold hiddenIndependentKernel
  infer_instance

/-- Factorization of the actual reference law, proved by iterated kernel
integration. It includes arbitrary private initial randomness. -/
theorem adaptiveKernelLaw_hidden_lintegral (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (Q : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (Q n)] :
    ∀ n (F : H × FiniteHistory S A n → ℝ≥0∞), Measurable F →
      (∫⁻ h, F ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)
        ∂adaptiveKernelLaw (ρ.prod μ) (hiddenIndependentKernel Q) n) =
      ∫⁻ θ, ∫⁻ h, F (θ,h) ∂adaptiveKernelLaw μ Q n ∂ρ := by
  intro n
  induction n with
  | zero =>
    intro F hF
    exact lintegral_prod _ hF.aemeasurable
  | succ n ih =>
    intro F hF
    let G : H × FiniteHistory S A n → ℝ≥0∞ :=
      fun z => ∫⁻ a, F (z.1,(z.2,a)) ∂Q n z.2
    have hG : Measurable G := by
      exact Measurable.lintegral_kernel_prod_right
        (κ := (Q n).comap Prod.snd measurable_snd)
        (hF.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)))
    change (∫⁻ h, F ((finiteHistoryInitial n h.1).1,
      (finiteHistoryMapInitial Prod.snd n h.1,h.2))
      ∂(adaptiveKernelLaw (ρ.prod μ) (hiddenIndependentKernel Q) n ⊗ₘ hiddenIndependentKernel Q n)) = _
    rw [Measure.lintegral_compProd]
    · change (∫⁻ h, G ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)
        ∂adaptiveKernelLaw (ρ.prod μ) (hiddenIndependentKernel Q) n) = _
      rw [ih G hG]
      apply lintegral_congr_ae
      filter_upwards [] with θ
      exact (Measure.lintegral_compProd (hF.comp measurable_prodMk_left)).symm
    · exact hF.comp ((measurable_fst.comp (finiteHistoryInitial_measurable n)).comp measurable_fst |>.prodMk
        (((finiteHistoryMapInitial_measurable measurable_snd n).comp measurable_fst).prodMk measurable_snd))

theorem hiddenIndependentKernel_reference_event (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (Q : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (Q n)]
    (n : ℕ) (E : H → FiniteHistory S A n → Prop)
    (hE : MeasurableSet {z : H × FiniteHistory S A n | E z.1 z.2}) {q : ℝ≥0∞}
    (htail : ∀ h, ρ {θ | E θ h} ≤ q) :
    adaptiveKernelLaw (ρ.prod μ) (hiddenIndependentKernel Q) n
      {h | E (finiteHistoryInitial n h).1 (finiteHistoryMapInitial Prod.snd n h)} ≤ q := by
  let F : H × FiniteHistory S A n → ℝ≥0∞ := {z | E z.1 z.2}.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hE
  have hm : MeasurableSet {h : FiniteHistory (H × S) A n |
      E (finiteHistoryInitial n h).1 (finiteHistoryMapInitial Prod.snd n h)} :=
    hE.preimage (historyHiddenPair_measurable n)
  rw [← lintegral_indicator_one hm]
  change (∫⁻ h, F ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)
    ∂adaptiveKernelLaw (ρ.prod μ) (hiddenIndependentKernel Q) n) ≤ _
  rw [adaptiveKernelLaw_hidden_lintegral ρ μ Q n F hF,
    lintegral_lintegral_swap (f := fun θ h => F (θ,h)) hF.aemeasurable]
  calc
    _ ≤ ∫⁻ _ : FiniteHistory S A n, q ∂adaptiveKernelLaw μ Q n := by
      apply lintegral_mono
      intro h
      change (∫⁻ θ, {θ | E θ h}.indicator (fun _ => 1) θ ∂ρ) ≤ _
      have ht : MeasurableSet {θ : H | E θ h} := hE.preimage measurable_prodMk_right
      rw [lintegral_indicator_const ht (1:ℝ≥0∞),one_mul]
      exact htail h
    _ = q := by simp

end
end SecondOrder
