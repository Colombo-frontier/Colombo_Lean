import SecondOrder.ReferenceActivation
import SecondOrder.FiniteReferenceIndependence
import SecondOrder.FirstOrderAdaptiveInformation

open MeasureTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section

theorem firstOrderBlockCompletion_activation_pmf {d : ℕ} (x : Point d) :
    pmfEventProbability (PMF.uniformOfFintype ((Fin d → Bool)))
      (fun θ => decide (0<firstOrderBlockCompletion θ x))≤2*Real.exp (-(d:ℝ)/128) := by
  rw [←pmfEventProbability_measure]
  simp only [decide_eq_true_eq]
  have hh := ENNReal.toReal_mono (by finiteness) (firstOrderBlockCompletion_activation_tail x)
  rw [ENNReal.toReal_ofReal (by positivity)] at hh
  exact hh

/-- Under a genuinely hidden-independent reference process, all adaptive
query points and the output together retain the original exponential tail.
The final-history representation allows arbitrary query/output maps. -/
theorem firstOrderReferenceActivation_probability {S A : Type} [Fintype S] [Fintype A] {d : ℕ}
    (p : PMF S) (K : ∀ n, FiniteHistory S A n → PMF A) (n : ℕ)
    (query : Fin (n+1) → FiniteHistory S A n → Point d) :
    pmfEventProbability
      (finiteAdaptiveLaw (finiteProdPMF (PMF.uniformOfFintype ((Fin d → Bool))) p)
        (hiddenIndependentTransition K) n)
      (fun h => decide (∃ i, 0<firstOrderBlockCompletion (finiteHistoryInitial n h).1
        (query i (finiteHistoryMapInitial Prod.snd n h))))≤
      (n+1:ℕ)*(2*Real.exp (-(d:ℝ)/128)) := by
  have hh := finiteReferenceEvents_probability (PMF.uniformOfFintype ((Fin d → Bool))) p K n
    (fun i θ h => decide (0<firstOrderBlockCompletion θ (query i h)))
    (fun i h => firstOrderBlockCompletion_activation_pmf (query i h))
  simpa only [decide_eq_true_eq, Fintype.card_fin] using hh

end
end SecondOrder

