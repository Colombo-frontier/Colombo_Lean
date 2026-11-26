import NCConcave16991.GlobalHardStageCalculus
import NCConcave16991.PipeSmoothness

/-! # The literal global finite-sum instance on the joint Euclidean product -/

namespace NCConcave16991.GlobalHard

noncomputable section

open scoped BigOperators InnerProductSpace ContDiff
open BranchGeometry

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {M N : ℕ} (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)]

abbrev PrimalStage (j : Fin M) := WithLp 2 (V j (Fin.last N) × PipeSmoothness.Connectors (V j))
abbrev Primal := PiLp 2 (PrimalStage V)
abbrev Dual := PiLp 2 (fun j : Fin M ↦ PipeSmoothness.Layers (V j))
abbrev Joint := WithLp 2 (Primal V × Dual V)

def stateProj (j : Fin M) : Joint V →L[ℝ] V j (Fin.last N) :=
  (WithLp.fstL 2 ℝ _ _).comp ((PiLp.proj 2 (PrimalStage V) j).comp (WithLp.fstL 2 ℝ _ _))

def connectorProj (j : Fin M) : Joint V →L[ℝ] PipeSmoothness.Connectors (V j) :=
  (WithLp.sndL 2 ℝ _ _).comp ((PiLp.proj 2 (PrimalStage V) j).comp (WithLp.fstL 2 ℝ _ _))

def dualProj (j : Fin M) : Joint V →L[ℝ] PipeSmoothness.Layers (V j) :=
  (PiLp.proj 2 _ j).comp (WithLp.sndL 2 ℝ _ _)

def pipeProj (j : Fin M) : Joint V →L[ℝ] PipeSmoothness.Joint (V j) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    ((connectorProj V j).prod (dualProj V j))

def aProj (j : Fin M) : Joint V →L[ℝ] V j 0 :=
  (PipeSmoothness.aProj).comp (pipeProj V j)

def bProj (j : Fin M) : Joint V →L[ℝ] V j (Fin.last N) :=
  (PipeSmoothness.bProj).comp (pipeProj V j)

def score (v : ∀ j, V j (Fin.last N)) (j : Fin M) (z : Joint V) : ℝ :=
  stateScore (v j) (stateProj V j z)

/-- The public score at index zero is one; there is no state-zero variable. -/
def precedingScore (v : ∀ j, V j (Fin.last N)) (j : Fin M) (z : Joint V) : ℝ :=
  Fin.cases 1 (fun k : Fin M ↦ score V v k z) j.castSucc

variable (B : ∀ j : Fin M, ∀ t : Fin N,
  BranchFamily (ι := ι) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))

/-- Each summand contains exactly the selected two-port component and all four
outer terms in equation E.51. Distinct stages retain distinct dual tuples. -/
def component (d r μ : ℝ) (i : ι) (z : Joint V) : ℝ :=
  ∑ j : Fin M, (PipeSmoothness.component (B j) d r μ i (pipeProj V j z) +
    outerStage (u j) (v j) (precedingScore V v j z) (stateProj V j z) (aProj V j z) (bProj V j z))

def average (d r μ : ℝ) (z : Joint V) : ℝ :=
  (1 / (Fintype.card ι : ℝ)) * ∑ i, component V B u v d r μ i z

theorem pipe_contDiff (d r μ : ℝ) (i : ι) (j : Fin M) :
    ContDiff ℝ ∞ (fun z : Joint V ↦ PipeSmoothness.component (B j) d r μ i (pipeProj V j z)) := by
  let q := PipeSmoothness.componentBilinear (B j) d r μ i
  have hq : ContDiff ℝ ∞ (fun z : PipeSmoothness.Joint (V j) ↦ q z z) :=
    q.contDiff.clm_apply contDiff_id
  have heq : (fun z : PipeSmoothness.Joint (V j) ↦ q z z) = PipeSmoothness.component (B j) d r μ i := by
    funext z
    exact PipeSmoothness.componentBilinear_diagonal (B j) d r μ i z
  rw [heq] at hq
  exact hq.comp (pipeProj V j).contDiff

theorem score_contDiff (j : Fin M) : ContDiff ℝ ∞ (score V v j) :=
  (stateScore_contDiff (v j)).comp (stateProj V j).contDiff

theorem precedingScore_contDiff (j : Fin M) : ContDiff ℝ ∞ (precedingScore V v j) := by
  unfold precedingScore
  generalize j.castSucc = k
  exact Fin.cases contDiff_const (fun k ↦ score_contDiff V v k) k

theorem component_contDiff (d r μ : ℝ) (i : ι) : ContDiff ℝ ∞ (component V B u v d r μ i) := by
  apply ContDiff.sum
  intro j _
  exact (pipe_contDiff V B d r μ i j).add
    (outerStage_contDiff (u j) (v j) _ _ _ _ (precedingScore_contDiff V v j)
      (stateProj V j).contDiff (aProj V j).contDiff (bProj V j).contDiff)

/-- The derivative is the actual Fréchet/Riesz gradient of the constructed
component; no derivative or regularity hypothesis is supplied. -/
theorem component_hasGradientAt (d r μ : ℝ) (i : ι) (z : Joint V) :
    HasGradientAt (component V B u v d r μ i) (gradient (component V B u v d r μ i) z) z :=
  ((component_contDiff V B u v d r μ i).differentiable (by simp) z).hasGradientAt

theorem average_contDiff (d r μ : ℝ) : ContDiff ℝ ∞ (average V B u v d r μ) :=
  contDiff_const.mul (ContDiff.sum fun i _ ↦ component_contDiff V B u v d r μ i)

end

end NCConcave16991.GlobalHard
