import NCConcave16991.AcceleratedParameters
import NCConcave16991.SaddleOperator

/-! # The accelerated certificate for an actual proximal saddle of the original Problem -/

noncomputable section

open Set
open scoped InnerProductSpace

namespace NCConcave16991.Accelerated

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}

/-- Restriction of the actual unsmoothed primal proximal saddle to a known compact convex region. -/
def compactProximalSaddle (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (region : Set (PrimalSpace dx)) (hne : region.Nonempty) (hcompact : IsCompact region)
    (hconvex : Convex ℝ region) (y0 : DualSpace dy) (c : PrimalSpace dx) :
    CompactSaddle (PrimalSpace dx) (DualSpace dy) where
  primal := region
  dual := K.carrier
  primal_nonempty := hne
  dual_nonempty := K.nonempty
  primal_compact := hcompact
  dual_compact := K.compact
  primal_convex := hconvex
  dual_convex := K.convex
  objective := saddleObjective P 0 y0 c
  gradientX x y := saddlePrimalGradient P c (jointPoint x y)
  gradientY x y := saddleDualGradient P 0 y0 (jointPoint x y)
  convexX y hy := by
    have hs := saddle_primal_stronglyConvex P hAS 0 y0 c y hy
    have hz : StrongConvexOn univ 0 (fun x ↦ saddleObjective P 0 y0 c x y) :=
      StrongConvexOn.mono p.L_pos.le hs
    exact (strongConvexOn_zero.mp hz).subset (subset_univ region) hconvex
  concaveY x hx := by
    convert (P.average_dual_concave x).add_const (p.L * ‖x - c‖ ^ 2) using 1
    ext y
    simp [saddleObjective, dualRegularizedSection]
  continuousX y hy := fun x hx ↦
    (saddle_primal_hasGradientAt P 0 y0 c x y hy).continuousAt.continuousWithinAt
  continuousY x hx := fun y hy ↦
    (saddle_dual_hasGradientAt P 0 y0 c x y hy).continuousAt.continuousWithinAt
  derivativeX x hx y hy := saddle_primal_hasGradientAt P 0 y0 c x y hy
  derivativeY x hx y hy := saddle_dual_hasGradientAt P 0 y0 c x y hy

 theorem compactProximalSaddle_objective (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (region : Set (PrimalSpace dx)) (hne : region.Nonempty) (hcompact : IsCompact region)
    (hconvex : Convex ℝ region) (y0 : DualSpace dy) (c x : PrimalSpace dx) (y : DualSpace dy) :
    (compactProximalSaddle P hAS region hne hcompact hconvex y0 c).objective x y =
      componentAverage P.component (jointPoint x y) + p.L * ‖x - c‖ ^ 2 := by
  simp [compactProximalSaddle, saddleObjective, dualRegularizedSection]

/-- Its primal maximum is exactly `Phi(x)+L||x-c||²`, with Phi the actual original maximum. -/
theorem compactProximalSaddle_primalValue (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (region : Set (PrimalSpace dx)) (hne : region.Nonempty) (hcompact : IsCompact region)
    (hconvex : Convex ℝ region) (y0 : DualSpace dy) (c : PrimalSpace dx)
    {x : PrimalSpace dx} (hx : x ∈ region) :
    primalValue (compactProximalSaddle P hAS region hne hcompact hconvex y0 c) x =
      primalObjective K P.component x + p.L * ‖x - c‖ ^ 2 := by
  let F := compactProximalSaddle P hAS region hne hcompact hconvex y0 c
  have hb : BddAbove ((fun y ↦ componentAverage P.component (jointPoint x y)) '' K.carrier) :=
    (K.compact.image_of_continuousOn (P.average_dual_continuous x)).bddAbove
  apply le_antisymm
  · apply csSup_le (K.nonempty.image _)
    rintro v ⟨y, hy, rfl⟩
    rw [compactProximalSaddle_objective]
    have h := le_csSup hb (show componentAverage P.component (jointPoint x y) ∈
      (fun y ↦ componentAverage P.component (jointPoint x y)) '' K.carrier from ⟨y, hy, rfl⟩)
    change componentAverage P.component (jointPoint x y) ≤ primalObjective K P.component x at h
    linarith
  · obtain ⟨y, hy, he⟩ := P.exists_dual_maximizer x
    have h := section_le_primal F hx hy
    change F.objective x y ≤ primalValue F x at h
    rw [compactProximalSaddle_objective, ← he] at h
    exact h

/-- On a genuine compact primal region, successful joint residual checks yield the
actual original proximal objective certificate against every feasible comparison point. -/
theorem actual_proximal_primal_certificate (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (region : Set (PrimalSpace dx)) (hne : region.Nonempty) (hcompact : IsCompact region)
    (hconvex : Convex ℝ region) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx)
    {τ δ DX : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) (hd : 0 < DX + p.diameter)
    (hDX : ∀ x ∈ region, ∀ u ∈ region, ‖x - u‖ ≤ DX)
    (solve : ℕ → DualSpace dy → ProxResult (X := PrimalSpace dx) (Y := DualSpace dy))
    (hcheck : ∀ k < horizon τ p.diameter δ,
      JointCheck (compactProximalSaddle P hAS region hne hcompact hconvex y0 c)
        τ (tolerance τ p.diameter δ (DX + p.diameter))
        (center τ k (states τ solve y0 k)) (resultAt τ solve y0 k))
    {x : PrimalSpace dx} (hx : x ∈ region) :
    primalObjective K P.component (primalOutput τ solve y0 (horizon τ p.diameter δ)) +
      p.L * ‖primalOutput τ solve y0 (horizon τ p.diameter δ) - c‖ ^ 2 ≤
      primalObjective K P.component x + p.L * ‖x - c‖ ^ 2 + δ := by
  let F := compactProximalSaddle P hAS region hne hcompact hconvex y0 c
  have hblock : ∀ k < horizon τ p.diameter δ,
      ResidualCheck F τ (tolerance τ p.diameter δ (DX + p.diameter))
        (center τ k (states τ solve y0 k)) (resultAt τ solve y0 k) :=
    fun k hk ↦ (hcheck k hk).toResidualCheck
  have hgap := source_primal_dual_gap F hτ hδ hd hDX K.diameter_bound solve hy0 hblock
  have hy := dual_feasible F solve hy0 hblock (le_rfl : horizon τ p.diameter δ ≤ horizon τ p.diameter δ)
  have hn := negative_section_le_dual F hx hy
  have hp := section_le_primal F hx hy
  have hb : primalValue F (primalOutput τ solve y0 (horizon τ p.diameter δ)) ≤ primalValue F x + δ := by linarith
  have hout := primalOutput_mem F hτ solve y0 (horizon_pos τ p.diameter δ) hblock
  have hlo := compactProximalSaddle_primalValue P hAS region hne hcompact hconvex y0 c hout
  have hhi := compactProximalSaddle_primalValue P hAS region hne hcompact hconvex y0 c hx
  change primalValue F (primalOutput τ solve y0 (horizon τ p.diameter δ)) = _ at hlo
  change primalValue F x = _ at hhi
  rw [hlo, hhi] at hb
  exact hb

end NCConcave16991.Accelerated


