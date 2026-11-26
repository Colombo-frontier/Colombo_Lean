import NCConcave16991.BranchOracleCoordinates

/-! # Exact Euclidean component replies from the released-source renderer -/

namespace NCConcave16991.BranchOracle
noncomputable section
open GlobalHard GlobalHardEuclidean
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

variable {n M N : ℕ} [NeZero n] (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, FiniteDimensional ℝ (V j k)]
variable {D : ℝ} (K : KnownDualDomain (dualDimension V) D)

def queryGlobal (q : OracleQuery n (primalDimension V) K) : GlobalHard.Joint V :=
  (jointCoordinates V).symm (queryPoint q)

def renderOracleAnswer (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N)) (d r μ : ℝ)
    (q : OracleQuery n (primalDimension V) K) (a : ∀ j, PipeActionData (V j)) :
    OracleAnswer (primalDimension V) (dualDimension V) :=
  let g := jointCoordinates V (renderComponentGradient (ι := Fin n) V u v d r μ (queryGlobal V K q) a)
  (renderComponentValue (ι := Fin n) V u v d r μ (queryGlobal V K q) a, (g.fst, g.snd))

variable (B : ∀ j : Fin M, ∀ t : Fin N,
    BranchGeometry.BranchFamily (ι := Fin n) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))

def trueComponentAnswer (d r μ : ℝ) (q : OracleQuery n (primalDimension V) K) :
    OracleAnswer (primalDimension V) (dualDimension V) :=
  let g := gradient (GlobalHardEuclidean.component V B u v d r μ q.1) (queryPoint q)
  (GlobalHardEuclidean.component V B u v d r μ q.1 (queryPoint q), (g.fst, g.snd))

def referenceResponse (r : ℕ) (d q μ : ℝ) (x : OracleQuery n (primalDimension V) K) :
    OracleAnswer (primalDimension V) (dualDimension V) :=
  renderOracleAnswer V K (knownIncoming V r u) (knownTerminal V r v) d q μ x
    (globalActionData V B x.1 (queryGlobal V K x))

theorem referenceResponse_eq_true_of_flat (r : ℕ) (d q μ : ℝ)
    (x : OracleQuery n (primalDimension V) K)
    (hflat : ∀ j : Fin M, r ≤ j.val →
      stateScore (v j) (stateProj V j (queryGlobal V K x)) < deltaGate) :
    referenceResponse V K B u v r d q μ x = trueComponentAnswer V K B u v d q μ x := by
  have heq := inactive_firstJet_rendered V B u v r d q μ x.1 (queryGlobal V K x) hflat
  have hv := congrArg Prod.fst heq
  have hg := congrArg Prod.snd heq
  dsimp only at hv hg
  have hcoord : gradient (GlobalHardEuclidean.component V B u v d q μ x.1) (queryPoint x) =
      jointCoordinates V (gradient (GlobalHard.component V B u v d q μ x.1) (queryGlobal V K x)) :=
    gradient_comp_isometry_symm (jointCoordinates V) (GlobalHard.component V B u v d q μ x.1) (queryPoint x)
      ((GlobalHard.component_contDiff V B u v d q μ x.1).differentiable (by simp) _)
  rw [hg] at hcoord
  apply Prod.ext
  · exact hv.symm
  · exact Prod.ext (congrArg WithLp.fst hcoord.symm) (congrArg WithLp.snd hcoord.symm)

end
end NCConcave16991.BranchOracle
