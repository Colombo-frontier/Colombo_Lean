import SampleReuse.TreeSampling

/-! Uniform accuracy of the actual sampled ancestor estimator for predictable
locations. All packet tail bounds are derived from Admissible, fresh disjoint
blocks, and the literal integer ceiling batch recipe. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {d M B : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}

theorem Admissible.gradient_tree_uniform_accuracy (h : Admissible μ P f F x₀)
    (z₀ : Ω) {η δ scale : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hscale : scale = confidenceBatchScale d (η / (binaryDepth M + 1)) (δ / (M + 1)))
    (hcap : B = batchSize scale (P.gradientNoise^2)) (hB : 0 < B)
    (y : ℕ → SampleTape ((M + 1) * B) Ω → Point d) (hy : PredictableLocations y) :
    (sampleTapeLaw ((M + 1) * B) μ).real {tape | ∃ k ≤ M,
      η < ‖sampledAncestorEstimate hB scale P.gradientNoise P.gradientLip
        (fun z => gradient (F z)) y tape k - gradient f (y k tape)‖} ≤ δ := by
  let θ := η / (binaryDepth M + 1)
  let ε := δ / (M + 1)
  have hθ : 0 < θ := div_pos hη (by positivity)
  have hε : 0 < ε := div_pos hδ (by positivity)
  have hs : 0 ≤ scale := by rw [hscale]; exact confidenceBatchScale_nonneg _ _ _
  have hrootSize : 32 * (matrixMomentOrder (d + 1) ε : ℝ) * P.gradientNoise^2 ≤
      (B : ℝ) * θ^2 := by
    simpa only [hcap, hscale] using
      (confidenceBatchSize_gradient_root d (σ := P.gradientNoise) (δ := ε) hθ)
  have hroot : (sampleTapeLaw ((M + 1) * B) μ).real {tape |
      θ ≤ ‖treeRootPacket (fun z => gradient (F z)) y tape - gradient f (y 0 tape)‖} ≤ ε := by
    have hr := h.gradient_root_confidence (y 0 (fun _ => z₀)) (treeBlockHandle M B 0)
      (treeBlockHandle_injective M B 0) hθ hε hB hrootSize
    simpa only [treeRootPacket, hy.root_constant z₀] using hr
  have hedge (k : ℕ) (hkpos : 0 < k) (hk : k ≤ M) :
      (sampleTapeLaw ((M + 1) * B) μ).real {tape |
        θ ≤ ‖treeChordPacket hB scale P.gradientNoise P.gradientLip (fun z => gradient (F z)) y k tape -
          (gradient f (y k tape) - gradient f (y (ancestorParent k) tape))‖} ≤ ε := by
    have hhist : Measurable (fun tape => (y k tape, y (ancestorParent k) tape)) :=
      (hy.measurable k hk).prodMk (hy.measurable _ ((ancestorParent_lt hkpos).le.trans hk))
    have hn : Measurable (fun xy : Point d × Point d =>
        chordBatchSize scale P.gradientNoise P.gradientLip xy.1 xy.2) :=
      chordBatchSize_measurable _ _ _ _ _ measurable_fst measurable_snd
    have hncap (xy : Point d × Point d) :
        chordBatchSize scale P.gradientNoise P.gradientLip xy.1 xy.2 ≤ B := by
      rw [hcap]
      exact chordBatchSize_le_capacity hs _ _ _ _
    have hnsize (xy : Point d × Point d) :
        32 * (matrixMomentOrder (d + 1) ε : ℝ) *
          (2 * min P.gradientNoise (P.gradientLip * ‖xy.1-xy.2‖))^2 ≤
        (chordBatchSize scale P.gradientNoise P.gradientLip xy.1 xy.2 : ℝ) * θ^2 := by
      rw [hscale]
      exact gradient_chordBatchSize_sufficient d hθ P.gradientNoise_pos.le P.gradientLip_pos.le _ _
    exact h.adaptive_gradient_chord_confidence hB z₀ (treePastHandles M B k)
      (fun tape => (y k tape, y (ancestorParent k) tape)) hhist
      (hy.pair_depends hk hkpos) (treeBlockHandle M B k) (treeBlockHandle_fresh hk)
      (treeBlockHandle_injective M B k) Prod.fst Prod.snd measurable_fst measurable_snd
      (fun xy => chordBatchSize scale P.gradientNoise P.gradientLip xy.1 xy.2) hn
      (fun xy => chordBatchSize_pos _ _ _ xy.1 xy.2) hncap hθ hε hnsize
  have hb := ancestorEstimate_uniform_probability (μ := sampleTapeLaw ((M + 1) * B) μ) M
    (fun tape k => gradient f (y k tape)) (treeRootPacket (fun z => gradient (F z)) y)
    (fun tape k => treeChordPacket hB scale P.gradientNoise P.gradientLip
      (fun z => gradient (F z)) y k tape) hη.le hroot hedge
  change (sampleTapeLaw ((M + 1) * B) μ).real {tape | ∃ k ≤ M,
    η < ‖ancestorEstimate (treeRootPacket (fun z => gradient (F z)) y tape)
      (fun j => treeChordPacket hB scale P.gradientNoise P.gradientLip
        (fun z => gradient (F z)) y j tape) k - gradient f (y k tape)‖} ≤ δ
  exact hb.trans_eq (by dsimp [ε]; push_cast; field_simp)

theorem Admissible.hessian_tree_uniform_accuracy (h : Admissible μ P f F x₀)
    (z₀ : Ω) {η δ scale : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hscale : scale = confidenceBatchScale d (η / (binaryDepth M + 1)) (δ / (M + 1)))
    (hcap : B = batchSize scale (P.hessianNoise^2)) (hB : 0 < B)
    (y : ℕ → SampleTape ((M + 1) * B) Ω → Point d) (hy : PredictableLocations y) :
    (sampleTapeLaw ((M + 1) * B) μ).real {tape | ∃ k ≤ M,
      η < ‖sampledAncestorEstimate hB scale P.hessianNoise P.hessianLip
        (fun z => hessian (F z)) y tape k - hessian f (y k tape)‖} ≤ δ := by
  let θ := η / (binaryDepth M + 1)
  let ε := δ / (M + 1)
  have hθ : 0 < θ := div_pos hη (by positivity)
  have hε : 0 < ε := div_pos hδ (by positivity)
  have hs : 0 ≤ scale := by rw [hscale]; exact confidenceBatchScale_nonneg _ _ _
  have hrootSize : 8 * (matrixMomentOrder (d + 1) ε : ℝ) * P.hessianNoise^2 ≤
      (B : ℝ) * θ^2 := by
    simpa only [hcap, hscale] using
      (confidenceBatchSize_hessian_root d (σ := P.hessianNoise) (δ := ε) hθ)
  have hroot : (sampleTapeLaw ((M + 1) * B) μ).real {tape |
      θ ≤ ‖treeRootPacket (fun z => hessian (F z)) y tape - hessian f (y 0 tape)‖} ≤ ε := by
    have hr := h.hessian_root_confidence (y 0 (fun _ => z₀)) (treeBlockHandle M B 0)
      (treeBlockHandle_injective M B 0) hθ hε hB hrootSize
    simpa only [treeRootPacket, hy.root_constant z₀] using hr
  have hedge (k : ℕ) (hkpos : 0 < k) (hk : k ≤ M) :
      (sampleTapeLaw ((M + 1) * B) μ).real {tape |
        θ ≤ ‖treeChordPacket hB scale P.hessianNoise P.hessianLip (fun z => hessian (F z)) y k tape -
          (hessian f (y k tape) - hessian f (y (ancestorParent k) tape))‖} ≤ ε := by
    have hhist : Measurable (fun tape => (y k tape, y (ancestorParent k) tape)) :=
      (hy.measurable k hk).prodMk (hy.measurable _ ((ancestorParent_lt hkpos).le.trans hk))
    have hn : Measurable (fun xy : Point d × Point d =>
        chordBatchSize scale P.hessianNoise P.hessianLip xy.1 xy.2) :=
      chordBatchSize_measurable _ _ _ _ _ measurable_fst measurable_snd
    have hncap (xy : Point d × Point d) :
        chordBatchSize scale P.hessianNoise P.hessianLip xy.1 xy.2 ≤ B := by
      rw [hcap]
      exact chordBatchSize_le_capacity hs _ _ _ _
    have hnsize (xy : Point d × Point d) :
        8 * (matrixMomentOrder (d + 1) ε : ℝ) *
          (2 * min P.hessianNoise (P.hessianLip * ‖xy.1-xy.2‖))^2 ≤
        (chordBatchSize scale P.hessianNoise P.hessianLip xy.1 xy.2 : ℝ) * θ^2 := by
      rw [hscale]
      exact hessian_chordBatchSize_sufficient d hθ P.hessianNoise_pos.le P.hessianLip_pos.le _ _
    exact h.adaptive_hessian_chord_confidence hB z₀ (treePastHandles M B k)
      (fun tape => (y k tape, y (ancestorParent k) tape)) hhist
      (hy.pair_depends hk hkpos) (treeBlockHandle M B k) (treeBlockHandle_fresh hk)
      (treeBlockHandle_injective M B k) Prod.fst Prod.snd measurable_fst measurable_snd
      (fun xy => chordBatchSize scale P.hessianNoise P.hessianLip xy.1 xy.2) hn
      (fun xy => chordBatchSize_pos _ _ _ xy.1 xy.2) hncap hθ hε hnsize
  have hb := ancestorEstimate_uniform_probability (μ := sampleTapeLaw ((M + 1) * B) μ) M
    (fun tape k => hessian f (y k tape)) (treeRootPacket (fun z => hessian (F z)) y)
    (fun tape k => treeChordPacket hB scale P.hessianNoise P.hessianLip
      (fun z => hessian (F z)) y k tape) hη.le hroot hedge
  change (sampleTapeLaw ((M + 1) * B) μ).real {tape | ∃ k ≤ M,
    η < ‖ancestorEstimate (treeRootPacket (fun z => hessian (F z)) y tape)
      (fun j => treeChordPacket hB scale P.hessianNoise P.hessianLip
        (fun z => hessian (F z)) y j tape) k - hessian f (y k tape)‖} ≤ δ
  exact hb.trans_eq (by dsimp [ε]; push_cast; field_simp)

end
end SampleReuse
