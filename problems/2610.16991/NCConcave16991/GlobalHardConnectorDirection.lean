import NCConcave16991.GlobalHardStateSection

/-! # The actual simultaneous connector direction and its exact norm -/

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

abbrev ConnectorTuple := PiLp 2 (fun j : Fin M ↦ PipeSmoothness.Connectors (V j))

def connectorTuple (z : Joint V) : ConnectorTuple V := WithLp.toLp 2 (fun j ↦ connectorProj V j z)

def primalConnectorInjection : ConnectorTuple V →ₗᵢ[ℝ] Primal V where
  toFun c := WithLp.toLp 2 (fun j ↦ WithLp.toLp 2 (0, c j))
  map_add' := by
    intro c d
    apply PiLp.ext
    intro j
    apply WithLp.ofLp_injective 2
    change ((0 : V j (Fin.last N)), c j + d j) = (0, c j) + (0, d j)
    simp
  map_smul' := by
    intro a c
    apply PiLp.ext
    intro j
    apply WithLp.ofLp_injective 2
    change ((0 : V j (Fin.last N)), a • c j) = a • (0, c j)
    simp
  norm_map' c := by
    change ‖(WithLp.toLp 2 (fun j ↦ WithLp.toLp 2 ((0 : V j (Fin.last N)), c j)) : Primal V)‖ = ‖c‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro j _
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp

def connectorInjection : ConnectorTuple V →L[ℝ] Joint V :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    ((primalConnectorInjection V).toContinuousLinearMap.prod (0 : ConnectorTuple V →L[ℝ] Dual V))

theorem connectorInjection_apply (c : ConnectorTuple V) :
    connectorInjection V c = WithLp.toLp 2 (primalConnectorInjection V c, 0) := rfl

theorem connectorInjection_norm (c : ConnectorTuple V) : ‖connectorInjection V c‖ = ‖c‖ := by
  rw [connectorInjection_apply]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp

theorem stateProj_connectorInjection (j : Fin M) (c : ConnectorTuple V) :
    stateProj V j (connectorInjection V c) = 0 := rfl

theorem connectorProj_connectorInjection (j : Fin M) (c : ConnectorTuple V) :
    connectorProj V j (connectorInjection V c) = c j := rfl

theorem dualProj_connectorInjection (j : Fin M) (c : ConnectorTuple V) :
    dualProj V j (connectorInjection V c) = 0 := rfl

theorem aProj_connectorInjection (j : Fin M) (c : ConnectorTuple V) :
    aProj V j (connectorInjection V c) = WithLp.fst (c j) := rfl

theorem bProj_connectorInjection (j : Fin M) (c : ConnectorTuple V) :
    bProj V j (connectorInjection V c) = WithLp.snd (c j) := rfl

def connectorRay (z : Joint V) (t : ℝ) : Joint V :=
  z + (t - 1) • connectorInjection V (connectorTuple V z)

theorem connectorRay_one (z : Joint V) : connectorRay V z 1 = z := by simp [connectorRay]

theorem stateProj_connectorRay (z : Joint V) (t : ℝ) (j : Fin M) :
    stateProj V j (connectorRay V z t) = stateProj V j z := by
  simp [connectorRay, stateProj_connectorInjection]

theorem dualProj_connectorRay (z : Joint V) (t : ℝ) (j : Fin M) :
    dualProj V j (connectorRay V z t) = dualProj V j z := by
  simp [connectorRay, dualProj_connectorInjection]

theorem connectorProj_connectorRay (z : Joint V) (t : ℝ) (j : Fin M) :
    connectorProj V j (connectorRay V z t) = t • connectorProj V j z := by
  simp only [connectorRay, map_add, map_smul, connectorProj_connectorInjection, connectorTuple, PiLp.toLp_apply]
  module

theorem aProj_connectorRay (z : Joint V) (t : ℝ) (j : Fin M) :
    aProj V j (connectorRay V z t) = t • aProj V j z := by
  change WithLp.fst (connectorProj V j (connectorRay V z t)) = t • WithLp.fst (connectorProj V j z)
  rw [connectorProj_connectorRay]
  rfl

theorem bProj_connectorRay (z : Joint V) (t : ℝ) (j : Fin M) :
    bProj V j (connectorRay V z t) = t • bProj V j z := by
  change WithLp.snd (connectorProj V j (connectorRay V z t)) = t • WithLp.snd (connectorProj V j z)
  rw [connectorProj_connectorRay]
  rfl

theorem precedingScore_connectorRay (v : ∀ j, V j (Fin.last N)) (z : Joint V) (t : ℝ) (j : Fin M) :
    precedingScore V v j (connectorRay V z t) = precedingScore V v j z := by
  by_cases hj : j.val = 0
  · rw [precedingScore_of_zero V v j hj, precedingScore_of_zero V v j hj]
  · rw [precedingScore_of_positive V v j hj, precedingScore_of_positive V v j hj,
      stateProj_connectorRay]

theorem connectorTuple_norm_sq (z : Joint V) :
    ‖connectorTuple V z‖ ^ 2 = ∑ j, (‖aProj V j z‖ ^ 2 + ‖bProj V j z‖ ^ 2) := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro j _
  rw [WithLp.prod_norm_sq_eq_of_L2]
  rfl

end
end NCConcave16991.GlobalHard
