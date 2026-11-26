import SampleReuse.TreeSamplingConfidence
import SampleReuse.OracleBatchDiagonalMeasurable

/-! Measurability of actual tree packets, cached estimates, and their uniform
accuracy events. This converts the proved failure bounds into success bounds. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

variable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {d M B : ℕ}

theorem treeRootPacket_measurable
    (sample : Ω → Point d → E) (hs : Measurable (fun w : Ω × Point d => sample w.1 w.2))
    (y : ℕ → SampleTape ((M + 1) * B) Ω → Point d) (hy : PredictableLocations y) :
    Measurable (treeRootPacket sample y) := by
  exact (Finset.measurable_sum _ (fun i _ => hs.comp
    ((measurable_pi_apply (treeBlockHandle M B 0 i)).prodMk (hy.measurable 0 (Nat.zero_le M))))).const_smul _

omit [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem treeChordPacket_eq_batchMean (hB : 0 < B) (scale σ L : ℝ)
    (sample : Ω → Point d → E) (y : ℕ → SampleTape ((M + 1) * B) Ω → Point d)
    (k : ℕ) (tape : SampleTape ((M + 1) * B) Ω) :
    treeChordPacket hB scale σ L sample y k tape =
      batchMeanTape (fun z => sample z (y k tape) - sample z (y (ancestorParent k) tape))
        (fun i : Fin (chordBatchSize scale σ L (y k tape) (y (ancestorParent k) tape)) =>
          treeBlockHandle M B k (prefixHandles hB _ i)) tape := rfl

theorem treeChordPacket_measurable (hB : 0 < B) (scale σ L : ℝ)
    (sample : Ω → Point d → E) (hs : Measurable (fun w : Ω × Point d => sample w.1 w.2))
    (y : ℕ → SampleTape ((M + 1) * B) Ω → Point d) (hy : PredictableLocations y)
    (k : ℕ) (hkpos : 0 < k) (hk : k ≤ M) :
    Measurable (treeChordPacket hB scale σ L sample y k) := by
  have hparent := hy.measurable (ancestorParent k) ((ancestorParent_lt hkpos).le.trans hk)
  have hn : Measurable (fun tape => chordBatchSize scale σ L (y k tape) (y (ancestorParent k) tape)) :=
    chordBatchSize_measurable scale σ L _ _ (hy.measurable k hk) hparent
  have hA : Measurable (fun w : SampleTape ((M + 1) * B) Ω × Ω =>
      sample w.2 (y k w.1) - sample w.2 (y (ancestorParent k) w.1)) :=
    (hs.comp (measurable_snd.prodMk ((hy.measurable k hk).comp measurable_fst))).sub
      (hs.comp (measurable_snd.prodMk (hparent.comp measurable_fst)))
  have ht : Measurable (fun tape : SampleTape ((M + 1) * B) Ω =>
      fun i : Fin B => tape (treeBlockHandle M B k i)) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (treeBlockHandle M B k i))
  have hc := adaptiveBatchMean_diagonal_measurable hB
    (fun tape z => sample z (y k tape) - sample z (y (ancestorParent k) tape)) hA
    (fun tape => chordBatchSize scale σ L (y k tape) (y (ancestorParent k) tape)) hn
    (fun tape i => tape (treeBlockHandle M B k i)) ht
  exact hc

theorem sampledAncestorEstimate_measurable (hB : 0 < B) (scale σ L : ℝ)
    (sample : Ω → Point d → E) (hs : Measurable (fun w : Ω × Point d => sample w.1 w.2))
    (y : ℕ → SampleTape ((M + 1) * B) Ω → Point d) (hy : PredictableLocations y)
    (k : ℕ) (hk : k ≤ M) :
    Measurable (fun tape => sampledAncestorEstimate hB scale σ L sample y tape k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      simpa only [sampledAncestorEstimate, ancestorEstimate] using treeRootPacket_measurable sample hs y hy
    | succ k =>
      have he (tape : SampleTape ((M + 1) * B) Ω) :
          sampledAncestorEstimate hB scale σ L sample y tape (k + 1) =
        sampledAncestorEstimate hB scale σ L sample y tape (ancestorParent (k + 1)) +
          treeChordPacket hB scale σ L sample y (k + 1) tape := by
        simp only [sampledAncestorEstimate, ancestorEstimate]
      simp_rw [he]
      exact (ih _ (ancestorParent_lt (Nat.succ_pos k))
        ((ancestorParent_lt (Nat.succ_pos k)).le.trans hk)).add
          (treeChordPacket_measurable hB scale σ L sample hs y hy (k + 1) (Nat.succ_pos k) hk)

theorem measurableSet_tree_accuracy_failure (hB : 0 < B) (scale σ L : ℝ)
    (sample : Ω → Point d → E) (hs : Measurable (fun w : Ω × Point d => sample w.1 w.2))
    (population : Point d → E) (hp : Measurable population)
    (y : ℕ → SampleTape ((M + 1) * B) Ω → Point d) (hy : PredictableLocations y) (η : ℝ) :
    MeasurableSet {tape | ∃ k ≤ M,
      η < ‖sampledAncestorEstimate hB scale σ L sample y tape k - population (y k tape)‖} := by
  have hk (k : Fin (M + 1)) : MeasurableSet {tape |
      η < ‖sampledAncestorEstimate hB scale σ L sample y tape k - population (y k tape)‖} :=
    measurableSet_lt measurable_const (((sampledAncestorEstimate_measurable hB scale σ L
      sample hs y hy k (by omega)).sub (hp.comp (hy.measurable k (by omega)))).norm)
  have he : {tape | ∃ k ≤ M,
      η < ‖sampledAncestorEstimate hB scale σ L sample y tape k - population (y k tape)‖} =
      ⋃ k : Fin (M + 1), {tape |
        η < ‖sampledAncestorEstimate hB scale σ L sample y tape k - population (y k tape)‖} := by
    ext tape
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨k, hkm, hfail⟩
      exact ⟨⟨k, by omega⟩, hfail⟩
    · rintro ⟨k, hfail⟩
      exact ⟨k, by omega, hfail⟩
  rw [he]
  exact MeasurableSet.iUnion hk

theorem uniform_success_of_failure_bound {Γ : Type*} [MeasurableSpace Γ]
    {ν : Measure Γ} [IsProbabilityMeasure ν] (error : ℕ → Γ → ℝ) (M : ℕ) (η δ : ℝ)
    (hm : MeasurableSet {w | ∃ k ≤ M, η < error k w})
    (hfail : ν.real {w | ∃ k ≤ M, η < error k w} ≤ δ) :
    1 - δ ≤ ν.real {w | ∀ k ≤ M, error k w ≤ η} := by
  have he : {w | ∀ k ≤ M, error k w ≤ η} = {w | ∃ k ≤ M, η < error k w}ᶜ := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_exists, not_and, not_lt]
  rw [he, measureReal_compl hm, measureReal_univ_eq_one]
  linarith

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}

theorem Admissible.gradient_tree_success (h : Admissible μ P f F x₀)
    (z₀ : Ω) {η δ scale : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hscale : scale = confidenceBatchScale d (η / (binaryDepth M + 1)) (δ / (M + 1)))
    (hcap : B = batchSize scale (P.gradientNoise^2)) (hB : 0 < B)
    (y : ℕ → SampleTape ((M + 1) * B) Ω → Point d) (hy : PredictableLocations y) :
    1 - δ ≤ (sampleTapeLaw ((M + 1) * B) μ).real {tape | ∀ k ≤ M,
      ‖sampledAncestorEstimate hB scale P.gradientNoise P.gradientLip
        (fun z => gradient (F z)) y tape k - gradient f (y k tape)‖ ≤ η} := by
  apply uniform_success_of_failure_bound
  · exact measurableSet_tree_accuracy_failure hB scale P.gradientNoise P.gradientLip _ h.gradient_measurable
      _ (contDiff_gradient_one h.population_smooth).continuous.measurable y hy η
  · exact h.gradient_tree_uniform_accuracy z₀ hη hδ hscale hcap hB y hy

theorem Admissible.hessian_tree_success (h : Admissible μ P f F x₀)
    (z₀ : Ω) {η δ scale : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hscale : scale = confidenceBatchScale d (η / (binaryDepth M + 1)) (δ / (M + 1)))
    (hcap : B = batchSize scale (P.hessianNoise^2)) (hB : 0 < B)
    (y : ℕ → SampleTape ((M + 1) * B) Ω → Point d) (hy : PredictableLocations y) :
    1 - δ ≤ (sampleTapeLaw ((M + 1) * B) μ).real {tape | ∀ k ≤ M,
      ‖sampledAncestorEstimate hB scale P.hessianNoise P.hessianLip
        (fun z => hessian (F z)) y tape k - hessian f (y k tape)‖ ≤ η} := by
  apply uniform_success_of_failure_bound
  · exact measurableSet_tree_accuracy_failure hB scale P.hessianNoise P.hessianLip _ h.hessian_measurable
      _ (continuous_hessian h.population_smooth).measurable y hy η
  · exact h.hessian_tree_uniform_accuracy z₀ hη hδ hscale hcap hB y hy

end
end SampleReuse
