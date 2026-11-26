import SecondOrder.CurvatureRandomEntryBound

open scoped Classical

namespace SecondOrder
noncomputable section

theorem finiteHistoryTape_prefix {S A : Type} (a₀ : A) (n k : ℕ)
    (h : FiniteHistory S A (n+k)) (t : ℕ) (ht : t<n) :
    finiteHistoryTape a₀ n (finiteHistoryPrefix n k h) t=finiteHistoryTape a₀ (n+k) h t := by
  have hh := finiteHistoryTape_append_prefix a₀ n (finiteHistoryPrefix n k h) k (finiteHistorySuffix n k h) t ht
  rw [finiteHistoryAppend_prefix_suffix] at hh
  exact hh.symm

theorem finiteHistoryTape_suffix {S A : Type} (a₀ : A) (n k : ℕ)
    (h : FiniteHistory S A (n+k)) (t : ℕ) (ht : t<k) :
    finiteHistoryTape a₀ k (finiteHistorySuffix n k h) t=finiteHistoryTape a₀ (n+k) h (n+t) := by
  have hh := finiteHistoryTape_append_suffix a₀ n (finiteHistoryPrefix n k h) k (finiteHistorySuffix n k h) t ht
  rw [finiteHistoryAppend_prefix_suffix] at hh
  exact hh.symm

variable {m T : ℕ} {S : Type*}

theorem curvatureStageEntry_tape_congr (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z z' : ℕ → CurvatureCoefficients m T R) (stage n : ℕ) (hz : ∀ t, t<n → z t=z' t) :
    curvatureStageEntry P Θ A β z stage n ↔ curvatureStageEntry P Θ A β z' stage n := by
  unfold curvatureStageEntry
  rw [curvatureComparisonRun_tape_congr P Θ A β z z' n hz,
    curvatureComparisonIndex_tape_congr P Θ A β z z' n hz]

def curvatureFastAfterEntry (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (z : ℕ → CurvatureCoefficients m T R) (i : Fin (T+1)) (cap n k : ℕ) : Prop :=
  let s := curvatureComparisonRun P Θ A β z n
  ∃ t, t≤k ∧ curvatureRestartFast P Θ A β n s.1 i cap s.2 t (fun u => z (n+u))

theorem curvatureEntryFutureFast_tape (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) (i : Fin (T+1)) (cap : ℕ) {R : ℝ}
    (a₀ : CurvatureCoefficients m T R) (n k : ℕ) (h : FiniteHistory Unit (CurvatureCoefficients m T R) (n+k)) :
    curvatureEntryFutureFast P Θ A β i cap a₀ n k h ↔
      curvatureFastAfterEntry P Θ A β (finiteHistoryTape a₀ (n+k) h) i cap n k := by
  unfold curvatureEntryFutureFast curvatureRestartFastEvent curvatureFastAfterEntry
  rw [curvatureComparisonRun_tape_congr P Θ A β _ _ n (finiteHistoryTape_prefix a₀ n k h)]
  apply exists_congr
  intro t
  constructor
  · rintro ⟨ht,hf⟩
    exact ⟨ht,(curvatureRestartFast_tape_congr P Θ A β n _ i cap _ t _ _
      (fun u hu => finiteHistoryTape_suffix a₀ n k h u (by omega))).mp hf⟩
  · rintro ⟨ht,hf⟩
    exact ⟨ht,(curvatureRestartFast_tape_congr P Θ A β n _ i cap _ t _ _
      (fun u hu => finiteHistoryTape_suffix a₀ n k h u (by omega))).mpr hf⟩

theorem curvatureStageEntry_prefix_probability (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (a₀ : CurvatureCoefficients m T R) (stage n k : ℕ) :
    pmfEventProbability (curvatureComparisonSamplingLaw P Θ A β R hR a₀ (n+k))
      (fun h => decide (curvatureStageEntry P Θ A β (finiteHistoryTape a₀ (n+k) h) stage n))=
    pmfEventProbability (curvatureComparisonSamplingLaw P Θ A β R hR a₀ n)
      (fun h => decide (curvatureStageEntry P Θ A β (finiteHistoryTape a₀ n h) stage n)) := by
  simp only [pmfEventProbability_mean, decide_eq_true_eq]
  unfold curvatureComparisonSamplingLaw
  rw [finiteAdaptiveLaw_continuation_mean]
  apply pmfMean_congr
  intro h
  have he (u : FiniteHistory Unit (CurvatureCoefficients m T R) k) :=
    curvatureStageEntry_tape_congr P Θ A β _ _ stage n (finiteHistoryTape_append_prefix a₀ n h k u)
  simp_rw [he]
  exact pmfMean_const _ _

end
end SecondOrder
