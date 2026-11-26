import FullJet.ExpectedAlgorithm

open MeasureTheory

namespace FullJet.StoppingJetAlgorithm

theorem measurable_countable_selection {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β]
    (g : ℕ → Ω → β) (hg : ∀ N, Measurable (g N)) (k : Ω → ℕ) (hk : Measurable k) :
    Measurable fun s => g (k s) s := by
  have hg' : Measurable (fun z : Ω × ℕ => g z.2 z.1) :=
    measurable_from_prod_countable (f := fun z : Ω × ℕ => g z.2 z.1) hg
  exact hg'.comp (measurable_id.prodMk hk)

variable {Ω E : Type} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E] {n p : ℕ}

theorem halts_measurable (A : StoppingJetAlgorithm Ω E n p) (f : Fin n → E → ℝ)
    (hobs : ∀ N, MeasurableSet {s | A.halt s (A.state f s N) = true}) :
    MeasurableSet {s | A.Halts f s} := by
  have heq : {s | A.Halts f s} = ⋃ N : ℕ, {s | A.halt s (A.state f s N) = true} := by
    ext s
    simp only [Halts, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [heq]
  exact MeasurableSet.iUnion hobs

theorem stopIndex_measurable (A : StoppingJetAlgorithm Ω E n p) (f : Fin n → E → ℝ)
    (hobs : ∀ N, MeasurableSet {s | A.halt s (A.state f s N) = true}) :
    Measurable (A.stopIndex f) := by
  classical
  apply measurable_of_Iic
  intro N
  have heq : (A.stopIndex f) ⁻¹' Set.Iic N =
      {s | ¬ A.Halts f s} ∪ {s | A.halt s (A.state f s N) = true} := by
    ext s
    change A.stopIndex f s ≤ N ↔ ¬ A.Halts f s ∨ A.halt s (A.state f s N) = true
    by_cases h : A.Halts f s
    · simp only [h, not_true_eq_false, false_or]
      exact ⟨A.halt_of_stopIndex_le f s h, A.stopIndex_le_of_halt f s⟩
    · simp [stopIndex, h]
  rw [heq]
  exact (A.halts_measurable f hobs).compl.union (hobs N)

theorem stoppedResult_eq_capped_result (A : StoppingJetAlgorithm Ω E n p)
    (f : Fin n → E → ℝ) (s : Ω) :
    A.stoppedResult f s = A.capped.result (A.stopIndex f s) f s := rfl

theorem stoppedGradient_measurable (A : StoppingJetAlgorithm Ω E n p) (f : Fin n → E → ℝ)
    (hobs : ∀ N, MeasurableSet {s | A.halt s (A.state f s N) = true})
    (hgrad : ∀ N, Measurable fun s => ‖fderiv ℝ (average f) (A.capped.result N f s)‖) :
    Measurable fun s => ‖fderiv ℝ (average f) (A.stoppedResult f s)‖ := by
  simp only [stoppedResult_eq_capped_result]
  exact measurable_countable_selection _ hgrad _ (A.stopIndex_measurable f hobs)

end FullJet.StoppingJetAlgorithm
