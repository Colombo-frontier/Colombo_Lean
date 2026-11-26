import NCConcave16991.AcceleratedParameters
import NCConcave16991.SVRGResidual

/-! # Explicit projected residuals supply the accelerated saddle checks -/

noncomputable section

open Set
open scoped InnerProductSpace

namespace NCConcave16991.Accelerated

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

abbrev ProductSpace (X Y : Type*) := WithLp 2 (X × Y)

def feasibleProduct (F : CompactSaddle X Y) : Set (ProductSpace X Y) :=
  {z | z.fst ∈ F.primal ∧ z.snd ∈ F.dual}

 theorem feasibleProduct_nonempty (F : CompactSaddle X Y) : (feasibleProduct F).Nonempty := by
  obtain ⟨x, hx⟩ := F.primal_nonempty
  obtain ⟨y, hy⟩ := F.dual_nonempty
  exact ⟨WithLp.toLp 2 (x, y), hx, hy⟩

 theorem feasibleProduct_closed (F : CompactSaddle X Y) : IsClosed (feasibleProduct F) :=
  (F.primal_compact.isClosed.preimage (WithLp.fstL 2 ℝ X Y).continuous).inter
    (F.dual_compact.isClosed.preimage (WithLp.sndL 2 ℝ X Y).continuous)

 theorem feasibleProduct_convex (F : CompactSaddle X Y) : Convex ℝ (feasibleProduct F) :=
  (F.primal_convex.linear_preimage (WithLp.fstL 2 ℝ X Y).toLinearMap).inter
    (F.dual_convex.linear_preimage (WithLp.sndL 2 ℝ X Y).toLinearMap)

/-- The actual signed saddle operator of the dual proximal subproblem. -/
def proximalOperator (F : CompactSaddle X Y) (τ : ℝ) (v : Y) (z : ProductSpace X Y) : ProductSpace X Y :=
  WithLp.toLp 2 (F.gradientX z.fst z.snd, -F.gradientY z.fst z.snd + τ • (z.snd - v))

/-- The explicit projected full step gives the feasible result and the two normal vectors. -/
def projectedResult (F : CompactSaddle X Y) (τ : ℝ) (v : Y) (ell : ℝ)
    (z : feasibleProduct F) : ProxResult (X := X) (Y := Y) :=
  let q := SVRG.fullStep (feasibleProduct F) (feasibleProduct_nonempty F) (feasibleProduct_closed F)
    (feasibleProduct_convex F) (proximalOperator F τ v) ell z
  let n := SVRG.fullStepNormal (feasibleProduct F) (feasibleProduct_nonempty F) (feasibleProduct_closed F)
    (feasibleProduct_convex F) (proximalOperator F τ v) ell z
  ⟨(q : ProductSpace X Y).fst, (q : ProductSpace X Y).snd, n.fst, n.snd⟩

/-- A product normal vector has a primal normal component, by testing a single-coordinate change. -/
theorem normalCone_primal {F : CompactSaddle X Y} {z n : ProductSpace X Y}
    (hz : z ∈ feasibleProduct F) (hn : n ∈ SVRG.normalCone (feasibleProduct F) z) :
    n.fst ∈ SVRG.normalCone F.primal z.fst := by
  intro x hx
  have h := hn (WithLp.toLp 2 (x, z.snd)) ⟨hx, hz.2⟩
  change ⟪n.fst, x - z.fst⟫_ℝ + ⟪n.snd, z.snd - z.snd⟫_ℝ ≤ 0 at h
  simpa using h

 theorem normalCone_dual {F : CompactSaddle X Y} {z n : ProductSpace X Y}
    (hz : z ∈ feasibleProduct F) (hn : n ∈ SVRG.normalCone (feasibleProduct F) z) :
    n.snd ∈ SVRG.normalCone F.dual z.snd := by
  intro y hy
  have h := hn (WithLp.toLp 2 (z.fst, y)) ⟨hz.1, hy⟩
  change ⟪n.fst, z.fst - z.fst⟫_ℝ + ⟪n.snd, y - z.snd⟫_ℝ ≤ 0 at h
  simpa using h

/-- The accelerated residual is exactly the solver's explicitly computed full-step residual. -/
theorem projectedResult_jointResidual (F : CompactSaddle X Y) (τ : ℝ) (v : Y) (ell : ℝ)
    (z : feasibleProduct F) :
    jointResidual F τ v (projectedResult F τ v ell z) =
      SVRG.fullStepResidual (feasibleProduct F) (feasibleProduct_nonempty F) (feasibleProduct_closed F)
        (feasibleProduct_convex F) (proximalOperator F τ v) ell z := by
  apply WithLp.ofLp_injective
  apply Prod.ext <;> rfl

/-- No normal-cone oracle is needed: the projected formula supplies all feasibility and normal facts. -/
theorem projectedResult_check (F : CompactSaddle X Y) (τ : ℝ) (v : Y) {ell ζ : ℝ}
    (hell : 0 < ell) (z : feasibleProduct F)
    (hr : ‖SVRG.fullStepResidual (feasibleProduct F) (feasibleProduct_nonempty F) (feasibleProduct_closed F)
      (feasibleProduct_convex F) (proximalOperator F τ v) ell z‖ ≤ ζ) :
    ResidualCheck F τ ζ v (projectedResult F τ v ell z) := by
  let q := SVRG.fullStep (feasibleProduct F) (feasibleProduct_nonempty F) (feasibleProduct_closed F)
    (feasibleProduct_convex F) (proximalOperator F τ v) ell z
  have hn := SVRG.fullStepNormal_mem (feasibleProduct F) (feasibleProduct_nonempty F) (feasibleProduct_closed F)
    (feasibleProduct_convex F) (proximalOperator F τ v) hell z
  apply residualCheck_of_joint F q.property.1 q.property.2
  · exact normalCone_primal q.property hn
  · exact normalCone_dual q.property hn
  · rw [projectedResult_jointResidual]
    exact hr

/-- The full source joint check is supplied by the explicit projected residual formula. -/
theorem projectedResult_jointCheck (F : CompactSaddle X Y) (τ : ℝ) (v : Y) {ell ζ : ℝ}
    (hell : 0 < ell) (z : feasibleProduct F)
    (hr : ‖SVRG.fullStepResidual (feasibleProduct F) (feasibleProduct_nonempty F) (feasibleProduct_closed F)
      (feasibleProduct_convex F) (proximalOperator F τ v) ell z‖ ≤ ζ) :
    JointCheck F τ ζ v (projectedResult F τ v ell z) := by
  let q := SVRG.fullStep (feasibleProduct F) (feasibleProduct_nonempty F) (feasibleProduct_closed F)
    (feasibleProduct_convex F) (proximalOperator F τ v) ell z
  have hn := SVRG.fullStepNormal_mem (feasibleProduct F) (feasibleProduct_nonempty F) (feasibleProduct_closed F)
    (feasibleProduct_convex F) (proximalOperator F τ v) hell z
  refine ⟨q.property.1, q.property.2, normalCone_primal q.property hn, normalCone_dual q.property hn, ?_⟩
  rw [projectedResult_jointResidual]
  exact hr

end NCConcave16991.Accelerated

