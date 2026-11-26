import NCConcave16991.GlobalHardConnectorDirection
import NCConcave16991.GlobalHardStateRestriction
import NCConcave16991.GlobalHardGap

/-! # Actual single-stage two-port directions and the exact averaged section -/

namespace NCConcave16991.GlobalHard
noncomputable section
open scoped BigOperators InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 800000

variable {M N : ℕ} (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)]

def portDirection (j : Fin M) (h : PipeSmoothness.Connectors (V j)) : Joint V :=
  connectorInjection V (PiLp.single 2 j h)

theorem portDirection_norm (j : Fin M) (h : PipeSmoothness.Connectors (V j)) :
    ‖portDirection V j h‖ = ‖h‖ := by rw [portDirection, connectorInjection_norm, PiLp.norm_single]

theorem portDirection_stateProj (j k : Fin M) (h : PipeSmoothness.Connectors (V j)) :
    stateProj V k (portDirection V j h) = 0 := stateProj_connectorInjection V k _

theorem portDirection_dualProj (j k : Fin M) (h : PipeSmoothness.Connectors (V j)) :
    dualProj V k (portDirection V j h) = 0 := dualProj_connectorInjection V k _

theorem portDirection_connectorProj_same (j : Fin M) (h : PipeSmoothness.Connectors (V j)) :
    connectorProj V j (portDirection V j h) = h := by rw [portDirection, connectorProj_connectorInjection, PiLp.single_eq_same]

theorem portDirection_connectorProj_ne (j k : Fin M) (hk : k ≠ j) (h : PipeSmoothness.Connectors (V j)) :
    connectorProj V k (portDirection V j h) = 0 := by rw [portDirection, connectorProj_connectorInjection, PiLp.single_eq_of_ne 2 hk]

def portRay (z : Joint V) (j : Fin M) (h : PipeSmoothness.Connectors (V j)) (t : ℝ) : Joint V :=
  z + (t - 1) • portDirection V j h

theorem portRay_one (z : Joint V) (j : Fin M) (h : PipeSmoothness.Connectors (V j)) : portRay V z j h 1 = z := by simp [portRay]

theorem stateProj_portRay (z : Joint V) (j k : Fin M) (h : PipeSmoothness.Connectors (V j)) (t : ℝ) :
    stateProj V k (portRay V z j h t) = stateProj V k z := by simp [portRay, portDirection_stateProj]

theorem dualProj_portRay (z : Joint V) (j k : Fin M) (h : PipeSmoothness.Connectors (V j)) (t : ℝ) :
    dualProj V k (portRay V z j h t) = dualProj V k z := by simp [portRay, portDirection_dualProj]

theorem connectorProj_portRay_same (z : Joint V) (j : Fin M) (h : PipeSmoothness.Connectors (V j)) (t : ℝ) :
    connectorProj V j (portRay V z j h t) = connectorProj V j z + (t - 1) • h := by
  simp [portRay, portDirection_connectorProj_same]

theorem connectorProj_portRay_ne (z : Joint V) (j k : Fin M) (hk : k ≠ j) (h : PipeSmoothness.Connectors (V j)) (t : ℝ) :
    connectorProj V k (portRay V z j h t) = connectorProj V k z := by
  simp [portRay, portDirection_connectorProj_ne V j k hk]

theorem aProj_portRay_same (z : Joint V) (j : Fin M) (h : PipeSmoothness.Connectors (V j)) (t : ℝ) :
    aProj V j (portRay V z j h t) = aProj V j z + (t - 1) • WithLp.fst h := by
  change WithLp.fst (connectorProj V j (portRay V z j h t)) = _
  rw [connectorProj_portRay_same]
  rfl

theorem bProj_portRay_same (z : Joint V) (j : Fin M) (h : PipeSmoothness.Connectors (V j)) (t : ℝ) :
    bProj V j (portRay V z j h t) = bProj V j z + (t - 1) • WithLp.snd h := by
  change WithLp.snd (connectorProj V j (portRay V z j h t)) = _
  rw [connectorProj_portRay_same]
  rfl

theorem precedingScore_portRay (v : ∀ j, V j (Fin.last N)) (z : Joint V)
    (j k : Fin M) (h : PipeSmoothness.Connectors (V j)) (t : ℝ) :
    precedingScore V v k (portRay V z j h t) = precedingScore V v k z := by
  by_cases hk : k.val = 0
  · rw [precedingScore_of_zero V v k hk, precedingScore_of_zero V v k hk]
  · rw [precedingScore_of_positive V v k hk, precedingScore_of_positive V v k hk, stateProj_portRay]

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  (B : ∀ j : Fin M, ∀ t : Fin N,
    BranchGeometry.BranchFamily (ι := ι) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))

theorem stageAverage_portRay_ne (d r μ : ℝ) (z : Joint V) (j k : Fin M) (hk : k ≠ j)
    (h : PipeSmoothness.Connectors (V j)) (t : ℝ) :
    stageAverage V B u v d r μ k (portRay V z j h t) = stageAverage V B u v d r μ k z := by
  have hp : pipeProj V k (portRay V z j h t) = pipeProj V k z := by
    change WithLp.toLp 2 (connectorProj V k (portRay V z j h t), dualProj V k (portRay V z j h t)) = _
    rw [connectorProj_portRay_ne V z j k hk, dualProj_portRay]
    rfl
  have ha : aProj V k (portRay V z j h t) = aProj V k z := by change WithLp.fst (connectorProj V k (portRay V z j h t)) = _; rw [connectorProj_portRay_ne V z j k hk]; rfl
  have hb : bProj V k (portRay V z j h t) = bProj V k z := by change WithLp.snd (connectorProj V k (portRay V z j h t)) = _; rw [connectorProj_portRay_ne V z j k hk]; rfl
  simp only [stageAverage, hp, precedingScore_portRay, stateProj_portRay, ha, hb]

theorem average_portRay_sub (d r μ : ℝ) (z : Joint V) (j : Fin M)
    (h : PipeSmoothness.Connectors (V j)) (t : ℝ) :
    average V B u v d r μ (portRay V z j h t) - average V B u v d r μ z =
      stageAverage V B u v d r μ j (portRay V z j h t) - stageAverage V B u v d r μ j z := by
  rw [average_eq_sum, average_eq_sum, ← Finset.sum_sub_distrib, Finset.sum_eq_single j]
  · intro k _ hkj
    rw [stageAverage_portRay_ne V B u v d r μ z j k hkj]
    ring
  · simp

end
end NCConcave16991.GlobalHard
