import SecondOrder.FiniteReferenceIndependence
import SecondOrder.CurvatureAdaptiveInformation

open MeasureTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section

theorem pmfEventProbability_union {A ι : Type*} [Fintype A] [Fintype ι]
    (p : PMF A) (E : ι → A → Bool) :
    pmfEventProbability p (fun a => decide (∃ i, E i a=true))≤∑ i, pmfEventProbability p (E i) := by
  rw [pmfEventProbability_mean]
  have hpoint (a : A) : (if decide (∃ i, E i a=true)=true then (1:ℝ) else 0)≤
      ∑ i, if E i a=true then (1:ℝ) else 0 := by
    by_cases he : ∃ i, E i a=true
    · obtain ⟨i,hi⟩ := he
      have hh := Finset.single_le_sum (f := fun j => if E j a=true then (1:ℝ) else 0)
        (fun j (_ : j ∈ Finset.univ) => by dsimp only; split_ifs <;> norm_num) (Finset.mem_univ i)
      simpa only [hi, if_true, decide_eq_true_eq, if_pos (show ∃ i, E i a=true from ⟨i,hi⟩)] using hh
    · simp only [decide_eq_true_eq, if_neg he]
      exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
  apply (pmfMean_mono p hpoint).trans_eq
  rw [pmfMean_finset_sum]
  exact Finset.sum_congr rfl (fun i _ => (pmfEventProbability_mean p (E i)).symm)

theorem finiteReferenceEvents_probability {H S A ι : Type} [Fintype H] [Fintype S] [Fintype A] [Fintype ι]
    (μ : PMF H) (p : PMF S) (K : ∀ n, FiniteHistory S A n → PMF A) (n : ℕ)
    (E : ι → H → FiniteHistory S A n → Bool) {q : ℝ}
    (hE : ∀ i h, pmfEventProbability μ (fun θ => E i θ h)≤q) :
    pmfEventProbability (finiteAdaptiveLaw (finiteProdPMF μ p) (hiddenIndependentTransition K) n)
      (fun h => decide (∃ i, E i (finiteHistoryInitial n h).1 (finiteHistoryMapInitial Prod.snd n h)=true))≤
      (Fintype.card ι:ℝ)*q := by
  apply (pmfEventProbability_union _ _).trans
  calc
    _ ≤ ∑ _i : ι, q := Finset.sum_le_sum (fun i _ => finiteReferenceEvent_probability μ p K n (E i) (hE i))
    _ = _ := by simp

theorem periodicCompletion_activation_pmf {m : ℕ} (x : Point (2*m)) :
    pmfEventProbability (PMF.uniformOfFintype (BalancedVector m))
      (fun θ => decide (0<periodicCompletion θ x))≤4*Real.exp (-((2*m:ℕ):ℝ)/512) := by
  rw [←pmfEventProbability_measure]
  simp only [decide_eq_true_eq]
  have hh := ENNReal.toReal_mono (by finiteness) (periodicCompletion_activation_tail x)
  rw [ENNReal.toReal_ofReal (by positivity)] at hh
  exact hh

/-- Under a genuinely hidden-independent reference process, all adaptive
query points and the output together retain the original exponential tail.
The final-history representation allows arbitrary query/output maps. -/
theorem curvatureReferenceActivation_probability {S A : Type} [Fintype S] [Fintype A] {m : ℕ}
    (p : PMF S) (K : ∀ n, FiniteHistory S A n → PMF A) (n : ℕ)
    (query : Fin (n+1) → FiniteHistory S A n → Point (2*m)) :
    pmfEventProbability
      (finiteAdaptiveLaw (finiteProdPMF (PMF.uniformOfFintype (BalancedVector m)) p)
        (hiddenIndependentTransition K) n)
      (fun h => decide (∃ i, 0<periodicCompletion (finiteHistoryInitial n h).1
        (query i (finiteHistoryMapInitial Prod.snd n h))))≤
      (n+1:ℕ)*(4*Real.exp (-((2*m:ℕ):ℝ)/512)) := by
  have hh := finiteReferenceEvents_probability (PMF.uniformOfFintype (BalancedVector m)) p K n
    (fun i θ h => decide (0<periodicCompletion θ (query i h)))
    (fun i h => periodicCompletion_activation_pmf (query i h))
  simpa only [decide_eq_true_eq, Fintype.card_fin] using hh

end
end SecondOrder
