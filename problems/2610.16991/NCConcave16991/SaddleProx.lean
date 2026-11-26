import NCConcave16991.SaddleSensitivity

/-! # The unbiased VI primal coordinate is the actual regularized proximal point -/

open Set InnerProductSpace
open scoped InnerProductSpace

namespace NCConcave16991

noncomputable section

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}

theorem saddleVI_cross_inequality (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {μ : ℝ} (hμ : 0 ≤ μ) (y0 : DualSpace dy) (c : PrimalSpace dx)
    (z : JointSpace dx dy)
    (hz : VariationalInequality.IsSolution (productDomain dx K) (tiltedSaddleOperator P μ y0 c 0) z)
    (w : JointSpace dx dy) (hw : w ∈ productDomain dx K) :
    saddleObjective P μ y0 c z.fst w.snd ≤ saddleObjective P μ y0 c w.fst z.snd := by
  have hL := p.L_pos
  have hs := saddleOperator_support P hAS μ y0 c z w hz.1 hw
  have hv := hz.2 w hw
  simp only [tiltedSaddleOperator, add_zero] at hv
  have he : z - w = -(w - z) := by abel
  rw [he, inner_neg_right] at hs
  have hc : 0 ≤ p.L / 2 * ‖z.fst - w.fst‖ ^ 2 + μ / 2 * ‖z.snd - w.snd‖ ^ 2 := by positivity
  linarith only [hs, hv, hc]

/-- The VI property implies the genuine minimization of the maximized
regularized objective with the primal proximal quadratic. -/
theorem saddleVI_primal_isProxPoint (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {μ : ℝ} (hμ : 0 ≤ μ) (y0 : DualSpace dy) (c : PrimalSpace dx)
    (z : JointSpace dx dy)
    (hz : VariationalInequality.IsSolution (productDomain dx K) (tiltedSaddleOperator P μ y0 c 0) z) :
    IsProxPoint (dualRegularizedValue P μ y0) p.L c z.fst := by
  have hmax : dualRegularizedValue P μ y0 z.fst = dualRegularizedSection P μ y0 z.fst z.snd := by
    apply le_antisymm _ (dualRegularizedSection_le_value P μ y0 z.fst z.snd hz.1)
    apply csSup_le (K.nonempty.image _)
    rintro v ⟨y, hy, rfl⟩
    have hd := saddleVI_cross_inequality P hAS hμ y0 c z hz (jointPoint z.fst y) hy
    change dualRegularizedSection P μ y0 z.fst y + p.L * ‖z.fst - c‖ ^ 2 ≤
      dualRegularizedSection P μ y0 z.fst z.snd + p.L * ‖z.fst - c‖ ^ 2 at hd
    linarith only [hd]
  intro x
  have hp := saddleVI_cross_inequality P hAS hμ y0 c z hz (jointPoint x z.snd) hz.1
  change dualRegularizedSection P μ y0 z.fst z.snd + p.L * ‖z.fst - c‖ ^ 2 ≤
    dualRegularizedSection P μ y0 x z.snd + p.L * ‖x - c‖ ^ 2 at hp
  have hval := dualRegularizedSection_le_value P μ y0 x z.snd hz.1
  change dualRegularizedValue P μ y0 z.fst + p.L * ‖z.fst - c‖ ^ 2 ≤
    dualRegularizedValue P μ y0 x + p.L * ‖x - c‖ ^ 2
  rw [hmax]
  linarith only [hp, hval]

theorem tiltedSaddleSolution_unbiased_primal_eq_proximalMap
    (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ p.L) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier)
    (c : PrimalSpace dx) :
    (tiltedSaddleSolution P hAS hμ hμL y0 c 0).fst =
      proximalMap p.L_pos (dualRegularizedValue_continuous P hAS μ y0)
        (dualRegularizedValue_bddBelow P hμ.le y0 hy0) c := by
  apply proxPoint_unique p.L_pos (dualRegularizedValue_weaklyConvex P hAS μ y0)
  · exact saddleVI_primal_isProxPoint P hAS hμ.le y0 c _
      (tiltedSaddleSolution_spec P hAS hμ hμL y0 c 0)
  · exact proximalMap_spec p.L_pos (dualRegularizedValue_continuous P hAS μ y0)
      (dualRegularizedValue_bddBelow P hμ.le y0 hy0) c

/-- The biased primal point is compared to the actual proximal point of Psi,
not merely to another unspecified VI vector. -/
theorem tiltedSaddleSolution_sensitivity_to_proximalMap
    (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ p.L) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier)
    (c : PrimalSpace dx) (ξ : JointSpace dx dy) :
    ‖(tiltedSaddleSolution P hAS hμ hμL y0 c ξ).fst -
        proximalMap p.L_pos (dualRegularizedValue_continuous P hAS μ y0)
          (dualRegularizedValue_bddBelow P hμ.le y0 hy0) c‖ ^ 2 ≤
      ‖ξ.fst‖ ^ 2 / p.L ^ 2 + ‖ξ.snd‖ ^ 2 / (p.L * μ) := by
  have h := tiltedSaddleSolution_primal_sensitivity P hAS hμ hμL y0 c ξ
  rwa [tiltedSaddleSolution_unbiased_primal_eq_proximalMap P hAS hμ hμL y0 hy0 c] at h

end

end NCConcave16991
