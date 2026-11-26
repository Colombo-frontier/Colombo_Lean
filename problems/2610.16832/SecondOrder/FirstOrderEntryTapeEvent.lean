import SecondOrder.CurvatureEntryTapeEvent
import SecondOrder.FirstOrderRandomEntryBound

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

theorem firstOrderStageEntry_tape_congr (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z z' : ℕ → FirstOrderCoefficients d T R) (stage n : ℕ) (hz : ∀ t, t<n → z t=z' t) :
    firstOrderStageEntry P Θ A β z stage n ↔ firstOrderStageEntry P Θ A β z' stage n := by
  unfold firstOrderStageEntry
  rw [firstOrderComparisonRun_tape_congr P Θ A β z z' n hz,
    firstOrderComparisonIndex_tape_congr P Θ A β z z' n hz]

def firstOrderFastAfterEntry (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (z : ℕ → FirstOrderCoefficients d T R) (i : Fin (T+1)) (cap n k : ℕ) : Prop :=
  let s := firstOrderComparisonRun P Θ A β z n
  ∃ t, t≤k ∧ firstOrderRestartFast P Θ A β n s.1 i cap s.2 t (fun u => z (n+u))

theorem firstOrderEntryFutureFast_tape (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) (i : Fin (T+1)) (cap : ℕ) {R : ℝ}
    (a₀ : FirstOrderCoefficients d T R) (n k : ℕ) (h : FiniteHistory Unit (FirstOrderCoefficients d T R) (n+k)) :
    firstOrderEntryFutureFast P Θ A β i cap a₀ n k h ↔
      firstOrderFastAfterEntry P Θ A β (finiteHistoryTape a₀ (n+k) h) i cap n k := by
  unfold firstOrderEntryFutureFast firstOrderRestartFastEvent firstOrderFastAfterEntry
  rw [firstOrderComparisonRun_tape_congr P Θ A β _ _ n (finiteHistoryTape_prefix a₀ n k h)]
  apply exists_congr
  intro t
  constructor
  · rintro ⟨ht,hf⟩
    exact ⟨ht,(firstOrderRestartFast_tape_congr P Θ A β n _ i cap _ t _ _
      (fun u hu => finiteHistoryTape_suffix a₀ n k h u (by omega))).mp hf⟩
  · rintro ⟨ht,hf⟩
    exact ⟨ht,(firstOrderRestartFast_tape_congr P Θ A β n _ i cap _ t _ _
      (fun u hu => finiteHistoryTape_suffix a₀ n k h u (by omega))).mpr hf⟩

theorem firstOrderStageEntry_prefix_probability (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (a₀ : FirstOrderCoefficients d T R) (stage n k : ℕ) :
    pmfEventProbability (firstOrderComparisonSamplingLaw P Θ A β R hR a₀ (n+k))
      (fun h => decide (firstOrderStageEntry P Θ A β (finiteHistoryTape a₀ (n+k) h) stage n))=
    pmfEventProbability (firstOrderComparisonSamplingLaw P Θ A β R hR a₀ n)
      (fun h => decide (firstOrderStageEntry P Θ A β (finiteHistoryTape a₀ n h) stage n)) := by
  simp only [pmfEventProbability_mean, decide_eq_true_eq]
  unfold firstOrderComparisonSamplingLaw
  rw [finiteAdaptiveLaw_continuation_mean]
  apply pmfMean_congr
  intro h
  have he (u : FiniteHistory Unit (FirstOrderCoefficients d T R) k) :=
    firstOrderStageEntry_tape_congr P Θ A β _ _ stage n (finiteHistoryTape_append_prefix a₀ n h k u)
  simp_rw [he]
  exact pmfMean_const _ _

end
end SecondOrder
