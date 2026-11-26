import NCConcave16991.GlobalHardPortDirection
import NCConcave16991.GlobalHardPortDerivative
import NCConcave16991.GlobalHardStateTransport

/-! # The actual global primal gradient controls both port derivatives -/

namespace NCConcave16991.GlobalHard
noncomputable section
open scoped BigOperators InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {M N : ℕ} (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)]
variable (B : ∀ j : Fin M, ∀ t : Fin N,
    BranchGeometry.BranchFamily (ι := ι) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))

def stageDualConstant (μ : ℝ) (j : Fin M) (z : Joint V) : ℝ :=
  -(BranchGeometry.beta ι / 2) * (μ * (∑ k, ‖dualProj V j z k‖ ^ 2) +
    ∑ t : Fin N, ‖dualProj V j z t.succ - (B j t).normalizedIsometry (dualProj V j z t.castSucc)‖ ^ 2)

theorem stageAverage_portRay_eq (d r μ : ℝ) (z : Joint V) (j : Fin M)
    (h : PipeSmoothness.Connectors (V j)) (t : ℝ) :
    stageAverage V B u v d r μ j (portRay V z j h t) =
      portObjective (u j) (v j) (precedingScore V v j z) (stateProj V j z) d r
        (dualProj V j z 0) (dualProj V j z (Fin.last N)) (stageDualConstant V B μ j z)
        (aProj V j z + (t - 1) • WithLp.fst h) (bProj V j z + (t - 1) • WithLp.snd h) := by
  have hp (q : Joint V) : (1 / (Fintype.card ι : ℝ)) * ∑ i,
      PipeSmoothness.component (B j) d r μ i (pipeProj V j q) =
      d * (‖aProj V j q‖ ^ 2 + ‖bProj V j q‖ ^ 2) +
        r * (⟪aProj V j q, dualProj V j q 0⟫_ℝ - ⟪bProj V j q, dualProj V j q (Fin.last N)⟫_ℝ) +
        stageDualConstant V B μ j q := by
    convert BranchGeometry.fullPipe_average (B j) d r μ (aProj V j q) (bProj V j q) (fun k ↦ dualProj V j q k) using 1 <;>
      first | rfl | (dsimp [stageDualConstant]; ring)
  unfold stageAverage
  rw [hp]
  simp only [stageDualConstant, dualProj_portRay, aProj_portRay_same, bProj_portRay_same,
    precedingScore_portRay, stateProj_portRay, portObjective]

theorem average_portRay_hasDerivAt (d r μ : ℝ) (z : Joint V) (j : Fin M)
    (h : PipeSmoothness.Connectors (V j)) :
    HasDerivAt (fun t : ℝ ↦ average V B u v d r μ (portRay V z j h t))
      (portDerivative (u j) (v j) (precedingScore V v j z) (stateProj V j z) d r
        (dualProj V j z 0) (dualProj V j z (Fin.last N)) (aProj V j z) (bProj V j z) (WithLp.fst h) (WithLp.snd h)) 1 := by
  have hh := (portObjective_hasDerivAt (u j) (v j) (precedingScore V v j z) (stateProj V j z) d r
    (dualProj V j z 0) (dualProj V j z (Fin.last N)) (stageDualConstant V B μ j z)
    (aProj V j z) (bProj V j z) (WithLp.fst h) (WithLp.snd h)).add_const
      (average V B u v d r μ z - stageAverage V B u v d r μ j z)
  convert hh using 1
  funext t
  have heq := average_portRay_sub V B u v d r μ z j h t
  rw [stageAverage_portRay_eq] at heq
  linarith

theorem portRay_split (z : Joint V) (j : Fin M) (h : PipeSmoothness.Connectors (V j)) (t : ℝ) :
    portRay V z j h t = WithLp.toLp 2
      (WithLp.fst z + (t - 1) • WithLp.fst (portDirection V j h), WithLp.snd z) := by
  apply WithLp.ofLp_injective 2
  change (WithLp.fst z + (t - 1) • WithLp.fst (portDirection V j h), WithLp.snd z + (t - 1) • 0) = _
  simp

theorem portDerivative_abs_le_primalGradient (d r μ : ℝ) (z : Joint V) (j : Fin M)
    (h : PipeSmoothness.Connectors (V j)) :
    |portDerivative (u j) (v j) (precedingScore V v j z) (stateProj V j z) d r
      (dualProj V j z 0) (dualProj V j z (Fin.last N)) (aProj V j z) (bProj V j z) (WithLp.fst h) (WithLp.snd h)| ≤
      ‖gradient (primalAverageSection V B u v d r μ (WithLp.snd z)) (WithLp.fst z)‖ * ‖h‖ := by
  let g := primalAverageSection V B u v d r μ (WithLp.snd z)
  let x := WithLp.fst z
  let k := WithLp.fst (portDirection V j h)
  have hg : HasGradientAt g (gradient g x) x :=
    ((primalAverageSection_contDiff V B u v d r μ (WithLp.snd z)).differentiable (by simp) x).hasGradientAt
  have hgg : HasFDerivAt g ((InnerProductSpace.toDual ℝ (Primal V)) (gradient g x)) (x + ((1 : ℝ) - 1) • k) := by
    simpa using hg.hasFDerivAt
  have hc := hgg.comp_hasDerivAt 1 (affine_direction_hasDerivAt x k)
  have hc' : HasDerivAt (fun t : ℝ ↦ average V B u v d r μ (portRay V z j h t)) ⟪gradient g x, k⟫_ℝ 1 := by
    convert hc using 1
    · funext t
      rw [portRay_split]
      rfl
    · simp only [InnerProductSpace.toDual_apply_apply]
  have heq := (average_portRay_hasDerivAt V B u v d r μ z j h).unique hc'
  rw [heq]
  have hn : ‖k‖ = ‖h‖ := by
    change ‖primalConnectorInjection V (PiLp.single 2 j h)‖ = ‖h‖
    rw [LinearIsometry.norm_map, PiLp.norm_single]
  simpa only [hn] using abs_real_inner_le_norm (gradient g x) k

end
end NCConcave16991.GlobalHard
