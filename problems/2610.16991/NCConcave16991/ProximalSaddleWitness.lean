import NCConcave16991.VanishingSaddle

/-! # An actual maximizing multiplier at the true proximal point

Compactness and vanishing dual regularization give a maximizing multiplier
whose primal gradient equals the original Moreau gradient. This is proved from
the actual components, without a maximum-rule or subgradient-selection premise.
-/

noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace NCConcave16991

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}

theorem proximal_saddle_witness (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (c : PrimalSpace dx) :
    ∃ y ∈ K.carrier,
      componentAverage P.component
        (jointPoint (proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c) y) =
        primalObjective K P.component
          (proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c) ∧
      Accelerated.primalMeanGradient P
        (proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c) y =
          gradient (problemMoreauEnvelope P) c := by
  obtain ⟨y0, hy0⟩ := K.nonempty
  let z := vanishingSaddle P hAS y0 c
  let x := proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c
  have hzmem (j : ℕ) : (z j).snd ∈ K.carrier := (vanishingSaddle_spec P hAS y0 c j).1
  obtain ⟨y, hy, φ, hφ, hyseq⟩ := K.compact.tendsto_subseq hzmem
  have hxseq : Tendsto (fun j ↦ (z (φ j)).fst) atTop (𝓝 x) :=
    (vanishingSaddle_primal_tendsto P hAS y0 hy0 c).comp hφ.tendsto_atTop
  have hjoint : Continuous (fun a : PrimalSpace dx × DualSpace dy ↦ jointPoint a.1 a.2) :=
    WithLp.prod_continuous_toLp 2 _ _
  have hzseq : Tendsto (fun j ↦ z (φ j)) atTop (𝓝 (jointPoint x y)) := by
    convert hjoint.continuousAt.tendsto.comp (hxseq.prodMk_nhds hyseq) using 1
    funext j
    rfl
  have hzwithin : Tendsto (fun j ↦ z (φ j)) atTop (𝓝[productDomain dx K] (jointPoint x y)) :=
    tendsto_nhdsWithin_iff.2 ⟨hzseq, Eventually.of_forall (fun j ↦ hzmem (φ j))⟩
  have hLip : LipschitzOnWith ⟨p.L, p.L_pos.le⟩ (averageMap P.componentGradient)
      (productDomain dx K) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    change dist (averageMap P.componentGradient a) (averageMap P.componentGradient b) ≤ p.L * dist a b
    simpa only [dist_eq_norm] using P.average_gradient_lipschitz hAS a ha b hb
  have hgseq := ((hLip.continuousOn _ hy).tendsto.comp hzwithin)
  have hgfst : Tendsto (fun j ↦ (averageMap P.componentGradient (z (φ j))).fst)
      atTop (𝓝 (Accelerated.primalMeanGradient P x y)) :=
    (WithLp.fstL 2 ℝ (PrimalSpace dx) (DualSpace dy)).continuous.continuousAt.tendsto.comp hgseq
  have hgsame : Tendsto (fun j ↦ (averageMap P.componentGradient (z (φ j))).fst)
      atTop (𝓝 ((2 * p.L) • (c - x))) := by
    have he (j : ℕ) : (averageMap P.componentGradient (z (φ j))).fst =
        (2 * p.L) • (c - (z (φ j)).fst) :=
      Accelerated.primalMeanGradient_at_saddle P _ y0 c _ (vanishingSaddle_spec P hAS y0 c (φ j))
    simp_rw [he]
    exact (tendsto_const_nhds.sub hxseq).const_smul (2 * p.L)
  have hgrad : Accelerated.primalMeanGradient P x y = gradient (problemMoreauEnvelope P) c := by
    rw [(P.moreau_hasGradientAt hAS c).gradient]
    exact tendsto_nhds_unique hgfst hgsame
  have hfseq : Tendsto (fun j ↦ componentAverage P.component (z (φ j))) atTop
      (𝓝 (componentAverage P.component (jointPoint x y))) :=
    (P.hasGradientAt_average (jointPoint x y) hy).continuousAt.tendsto.comp hzseq
  have hmax (v : DualSpace dy) (hv : v ∈ K.carrier) :
      componentAverage P.component (jointPoint x v) ≤
        componentAverage P.component (jointPoint x y) := by
    have hxv : Tendsto (fun j ↦ jointPoint (z (φ j)).fst v) atTop (𝓝 (jointPoint x v)) :=
      hjoint.continuousAt.tendsto.comp (hxseq.prodMk_nhds tendsto_const_nhds)
    have hfv := (P.hasGradientAt_average (jointPoint x v) hv).continuousAt.tendsto.comp hxv
    have hμ := (vanishingRegularization_tendsto p).comp hφ.tendsto_atTop
    have herr : Tendsto (fun j ↦ vanishingRegularization p (φ j) / 2 * ‖v - y0‖ ^ 2)
        atTop (𝓝 0) := by
      simpa only [zero_div, zero_mul, Function.comp_def] using (hμ.div_const 2).mul_const (‖v - y0‖ ^ 2)
    have hright : Tendsto (fun j ↦ componentAverage P.component (z (φ j)) +
        vanishingRegularization p (φ j) / 2 * ‖v - y0‖ ^ 2) atTop
        (𝓝 (componentAverage P.component (jointPoint x y))) := by
      simpa only [add_zero] using hfseq.add herr
    apply le_of_tendsto_of_tendsto hfv hright
    apply Eventually.of_forall
    intro j
    have hs := saddleVI_cross_inequality P hAS (vanishingRegularization_pos p (φ j)).le
      y0 c (z (φ j)) (vanishingSaddle_spec P hAS y0 c (φ j))
      (jointPoint (z (φ j)).fst v) hv
    change componentAverage P.component (jointPoint (z (φ j)).fst v) -
        vanishingRegularization p (φ j) / 2 * ‖v - y0‖ ^ 2 +
        p.L * ‖(z (φ j)).fst - c‖ ^ 2 ≤
      componentAverage P.component (z (φ j)) -
        vanishingRegularization p (φ j) / 2 * ‖(z (φ j)).snd - y0‖ ^ 2 +
        p.L * ‖(z (φ j)).fst - c‖ ^ 2 at hs
    have hn : 0 ≤ vanishingRegularization p (φ j) / 2 * ‖(z (φ j)).snd - y0‖ ^ 2 := by
      exact mul_nonneg (div_nonneg (vanishingRegularization_pos p (φ j)).le (by norm_num)) (sq_nonneg _)
    dsimp only [Function.comp_apply]
    linarith only [hs, hn]
  refine ⟨y, hy, le_antisymm (componentAverage_le_primalObjective P x y hy) ?_, hgrad⟩
  apply csSup_le (K.nonempty.image _)
  rintro v ⟨v, hv, rfl⟩
  exact hmax v hv

/-- A successful arbitrary output has an actual nearby maximizing saddle with
a small primal gradient. The displacement is measured at the original output. -/
theorem stationaryOutput_proximal_witness (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (c : PrimalSpace dx) (hc : StationaryOutput P c) :
    ∃ y ∈ K.carrier,
      componentAverage P.component
        (jointPoint (proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c) y) =
        primalObjective K P.component
          (proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c) ∧
      ‖Accelerated.primalMeanGradient P
        (proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c) y‖ ≤ p.epsilon ∧
      ‖proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c - c‖ ≤
        p.epsilon / (2 * p.L) := by
  obtain ⟨y, hy, hmax, hg⟩ := proximal_saddle_witness P hAS c
  have hn := (P.stationaryOutput_iff hAS c).1 hc
  refine ⟨y, hy, hmax, ?_, ?_⟩
  · rw [hg]
    exact hn
  · rw [(P.moreau_hasGradientAt hAS c).gradient, norm_smul, Real.norm_eq_abs,
      abs_of_pos (show 0 < 2 * p.L by linarith [p.L_pos]), norm_sub_rev] at hn
    apply (le_div_iff₀ (show 0 < 2 * p.L by linarith [p.L_pos])).2
    nlinarith only [hn]

end NCConcave16991
