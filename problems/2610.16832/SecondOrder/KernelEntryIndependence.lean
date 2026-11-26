import SecondOrder.KernelHiddenIndependence
import SecondOrder.KernelSurvival

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

universe u
namespace SecondOrder
noncomputable section
variable {H S A : Type u} [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace A]

/-- The fresh hidden parameter and the full reference transcript have the
actual product law, not merely matching individual marginal laws. -/
theorem adaptiveKernelLaw_hidden_map (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (Q : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (Q n)] (n : ℕ) :
    (adaptiveKernelLaw (ρ.prod μ) (hiddenIndependentKernel Q) n).map
      (fun h => ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)) =
      ρ.prod (adaptiveKernelLaw μ Q n) := by
  ext E hE
  rw [Measure.map_apply (historyHiddenPair_measurable n) hE,
    ←lintegral_indicator_one (hE.preimage (historyHiddenPair_measurable n))]
  let F : H × FiniteHistory S A n → ℝ≥0∞ := E.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hE
  change (∫⁻ h, F ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)
    ∂adaptiveKernelLaw (ρ.prod μ) (hiddenIndependentKernel Q) n) = _
  rw [adaptiveKernelLaw_hidden_lintegral ρ μ Q n F hF,←lintegral_prod _ hF.aemeasurable]
  exact lintegral_indicator_const hE (1:ℝ≥0∞) |>.trans (one_mul _)

/-- Restricting a reference interaction to a public entry event keeps the
fresh parameter independent, with the original prior. The entry measure is
left unnormalised, so entries of probability zero are covered as well. -/
theorem adaptiveKernelLaw_hidden_entry_map (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (Q : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (Q n)]
    (n : ℕ) {E : Set (FiniteHistory S A n)} (hE : MeasurableSet E) :
    ((adaptiveKernelLaw (ρ.prod μ) (hiddenIndependentKernel Q) n).restrict
      (finiteHistoryMapInitial Prod.snd n ⁻¹' E)).map
      (fun h => ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)) =
      ρ.prod ((adaptiveKernelLaw μ Q n).restrict E) := by
  have he : finiteHistoryMapInitial Prod.snd n ⁻¹' E =
      (fun h : FiniteHistory (H × S) A n =>
        ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)) ⁻¹' (Set.univ ×ˢ E) := by
    ext h
    simp only [Set.mem_preimage,Set.mem_prod,Set.mem_univ,true_and]
  rw [he,←Measure.restrict_map (historyHiddenPair_measurable n) (MeasurableSet.univ.prod hE),
    adaptiveKernelLaw_hidden_map ρ μ Q n,←Measure.prod_restrict,Measure.restrict_univ]

theorem kernelSurvivalSet_hidden (safe : ∀ n, Set (FiniteHistory S A n)) :
    ∀ n, kernelSurvivalSet (fun n => finiteHistoryMapInitial (A := A) (S := H × S) Prod.snd n ⁻¹' safe n) n =
      finiteHistoryMapInitial Prod.snd n ⁻¹' kernelSurvivalSet safe n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    ext h
    simp only [kernelSurvivalSet,Set.mem_inter_iff,Set.mem_preimage,ih,finiteHistoryMapInitial]

theorem kernelBeforeSet_hidden (safe : ∀ n, Set (FiniteHistory S A n)) (n : ℕ) :
    kernelBeforeSet (fun n => finiteHistoryMapInitial (A := A) (S := H × S) Prod.snd n ⁻¹' safe n) n =
      finiteHistoryMapInitial Prod.snd n ⁻¹' kernelBeforeSet safe n := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [kernelBeforeSet,kernelSurvivalSet_hidden]
    rfl

/-- Before an entry can use its first informative reply, agreement with
public kernels proves independence of the fresh block on every entry event.
No conditional independence or regular conditional law is assumed. -/
theorem adaptiveKernelLaw_entry_independent (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (FiniteHistory (H × S) A n) A)
    (Q : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] [∀ n, IsMarkovKernel (Q n)]
    (safe : ∀ n, Set (FiniteHistory S A n)) (hs : ∀ n, MeasurableSet (safe n))
    (heq : ∀ n h, finiteHistoryMapInitial Prod.snd n h ∈ safe n →
      K n h = Q n (finiteHistoryMapInitial Prod.snd n h))
    (n : ℕ) {E : Set (FiniteHistory S A n)} (hE : MeasurableSet E)
    (hsub : E ⊆ kernelBeforeSet safe n) :
    ((adaptiveKernelLaw (ρ.prod μ) K n).restrict (finiteHistoryMapInitial Prod.snd n ⁻¹' E)).map
      (fun h => ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)) =
      ρ.prod ((adaptiveKernelLaw μ Q n).restrict E) := by
  let liftedSafe := fun n => finiteHistoryMapInitial (A := A) (S := H × S) Prod.snd n ⁻¹' safe n
  have hl : ∀ n, MeasurableSet (liftedSafe n) :=
    fun n => (hs n).preimage (finiteHistoryMapInitial_measurable measurable_snd n)
  have ha := adaptiveKernelLaw_before_eq (ρ.prod μ) K (hiddenIndependentKernel Q)
    liftedSafe hl heq n
  have ht : finiteHistoryMapInitial (A := A) (S := H × S) Prod.snd n ⁻¹' E ⊆
      kernelBeforeSet liftedSafe n := by
    rw [kernelBeforeSet_hidden]
    exact Set.preimage_mono hsub
  have hr := congrArg (fun η : Measure (FiniteHistory (H × S) A n) =>
    η.restrict (finiteHistoryMapInitial Prod.snd n ⁻¹' E)) ha
  simp only [Measure.restrict_restrict_of_subset ht] at hr
  rw [hr]
  exact adaptiveKernelLaw_hidden_entry_map ρ μ Q n hE

end
end SecondOrder
