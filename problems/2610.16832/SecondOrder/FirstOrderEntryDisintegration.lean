import SecondOrder.FirstOrderComparisonRestartLaw
import SecondOrder.ParameterizedAdaptiveLaw

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

/-- Exact disintegration at a specified stage-entry time. The entry history
is sampled under the original comparison law; the target vector is freshly
averaged from its prior, and the continuation restarts from the actual entry
state. No independence of the continuation itself is asserted. -/
theorem firstOrderStageEntry_conditional_mean (μ : PMF ((Fin d → Bool))) (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (a₀ : FirstOrderCoefficients d T R) (i : Fin (T+1)) (n k : ℕ)
    (F : (Fin d → Bool) → FiniteHistory Unit (FirstOrderCoefficients d T R) (n+k) → ℝ) :
    pmfMean (firstOrderCoordinateSamplingLaw μ P Θ A β R hR a₀ i (n+k))
      (fun w => if firstOrderStageEntry P (Function.update Θ i w.1) A β
        (finiteHistoryTape a₀ n (finiteHistoryPrefix n k w.2)) i.val n then F w.1 w.2 else 0)=
    pmfMean (firstOrderComparisonSamplingLaw P Θ A β R hR a₀ n)
      (fun h => if firstOrderStageEntry P Θ A β (finiteHistoryTape a₀ n h) i.val n then
        pmfMean μ (fun θ => pmfMean
          (firstOrderRestartSamplingLaw P (Function.update Θ i θ) A β R hR n
            (firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).1
            (firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).2 k)
          (fun u => F θ (finiteHistoryAppend n h k u))) else 0) := by
  let K := fun θ => firstOrderComparisonTransition P (Function.update Θ i θ) A β R hR a₀
  let E := fun θ (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n) =>
    firstOrderStageEntry P (Function.update Θ i θ) A β (finiteHistoryTape a₀ n h) i.val n
  have he (θ : (Fin d → Bool)) h : E θ h ↔ E (Θ i) h :=
    firstOrderStageEntry_iff_prefix P _ _ A β _ i.val n (firstOrderHidden_update_prefix Θ i θ (Θ i))
  have hk (θ : (Fin d → Bool)) h (hh : E (Θ i) h) :
      finiteAdaptiveLaw (PMF.pure ()) (K θ) n h=finiteAdaptiveLaw (PMF.pure ()) (K (Θ i)) n h := by
    have hd := firstOrderStageEntry_mass_prefix P (Function.update Θ i θ) (Function.update Θ i (Θ i))
      A β R hR a₀ i.val n h (firstOrderHidden_update_prefix Θ i θ (Θ i))
    rw [if_pos ((he θ h).mpr hh), if_pos hh] at hd
    exact hd
  have hh := finiteHiddenContinuation_mean μ (PMF.pure ()) K (Θ i) n k E F he hk
  simp only [K, E, Function.update_eq_self] at hh
  refine hh.trans ?_
  apply pmfMean_congr
  intro h
  by_cases hent : firstOrderStageEntry P Θ A β (finiteHistoryTape a₀ n h) i.val n
  · rw [if_pos hent, if_pos hent]
    apply pmfMean_congr
    intro θ
    rw [firstOrderComparison_continuation_law]
    have hprefix : ∀ j, j.val < i.val → Function.update Θ i θ j=Θ j := by
      intro j hj
      have hne : j≠i := by intro heq; subst j; omega
      simp only [Function.update_of_ne hne]
    have hs := (firstOrderStageEntry_prefix P Θ (Function.update Θ i θ) A β
      (finiteHistoryTape a₀ n h) i.val n (fun j hj => (hprefix j hj).symm) hent).2
    rw [←hs]
  · rw [if_neg hent, if_neg hent]

end
end SecondOrder
