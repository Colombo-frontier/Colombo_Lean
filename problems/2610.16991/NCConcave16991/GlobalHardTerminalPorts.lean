import NCConcave16991.GlobalHardPortGradient
import NCConcave16991.GlobalHardInteriority
import NCConcave16991.BranchConstructionOptimizerSource

/-! # The two actual frontier connector equations at a maximizing witness -/

namespace NCConcave16991.GlobalHard
noncomputable section
open LocalizationScalar LocalizationRadial LocalizationHessian
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {M m : ℕ} (V : Fin M → Fin ((m + 1) + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)] [∀ j k, FiniteDimensional ℝ (V j k)]
variable (B : ∀ j : Fin M, ∀ t : Fin (m + 1),
    BranchGeometry.BranchFamily (ι := ι) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last (m + 1)))

theorem ports_norm_le_connectorTuple (z : Joint V) (j : Fin M) :
    ‖aProj V j z‖ ≤ ‖connectorTuple V z‖ ∧ ‖bProj V j z‖ ≤ ‖connectorTuple V z‖ := by
  have hj : ‖connectorProj V j z‖ ≤ ‖connectorTuple V z‖ := PiLp.norm_apply_le (p := 2) (connectorTuple V z) j
  exact ⟨(WithLp.norm_fst_le (p := 2) (α := _) (β := _) (connectorProj V j z)).trans hj,
    (WithLp.norm_snd_le (p := 2) (α := _) (β := _) (connectorProj V j z)).trans hj⟩

theorem portDerivative_left_at_optimizer (z : Joint V) (j : Fin M)
    (hu : ‖u j‖ = 1) (hprop : v j = BranchConstruction.terminalTransport (V j) (B j) (u j))
    (hw : WithLp.snd z = globalPaperOptimizer V B z) (ha : ‖aProj V j z‖ ≤ 21)
    (hL : activationLoad (precedingScore V v j z) (score V v j z) = 1) :
    portDerivative (u j) (v j) (precedingScore V v j z) (stateProj V j z) (EndpointConstants.endpointD m)
      (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
      (dualProj V j z 0) (dualProj V j z (Fin.last (m + 1))) (aProj V j z) (bProj V j z) (u j) 0 =
      2 * ⟪aProj V j z, u j⟫_ℝ - ⟪bProj V j z, v j⟫_ℝ - 4 := by
  have hwj : dualProj V j z = BranchConstruction.paperOptimizer (V j) (B j) (aProj V j z) (bProj V j z) := by
    change WithLp.snd z j = _
    rw [hw]
    rfl
  have hr := BranchConstruction.paperOptimizer_root_source (V j) (B j) (aProj V j z) (u j) (bProj V j z)
  rw [← hwj, ← hprop] at hr
  have hcap := radialCap_fderiv_identity (by norm_num : (0 : ℝ) < 21) (aProj V j z) ha
  have huu : ⟪u j, u j⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  change activationLoad (precedingScore V v j z) (stateScore (v j) (stateProj V j z)) = 1 at hL
  simp only [portDerivative, portOuterDerivative, inner_zero_right, inner_zero_left, map_zero,
    hcap, ContinuousLinearMap.id_apply, huu, hL, mul_one, zero_add, add_zero, mul_zero, sub_zero]
  dsimp [EndpointConstants.endpointD]
  nlinarith only [hr]

theorem portDerivative_right_at_optimizer (z : Joint V) (j : Fin M)
    (hprop : v j = BranchConstruction.terminalTransport (V j) (B j) (u j))
    (hw : WithLp.snd z = globalPaperOptimizer V B z) (hb : ‖bProj V j z‖ ≤ 21)
    (hs : ‖stateProj V j z‖ ≤ 10)
    (hL : activationLoad (precedingScore V v j z) (score V v j z) = 1) :
    portDerivative (u j) (v j) (precedingScore V v j z) (stateProj V j z) (EndpointConstants.endpointD m)
      (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
      (dualProj V j z 0) (dualProj V j z (Fin.last (m + 1))) (aProj V j z) (bProj V j z) 0 (v j) =
      -⟪aProj V j z, u j⟫_ℝ + 2 * ⟪bProj V j z, v j⟫_ℝ - score V v j z := by
  have hwj : dualProj V j z = BranchConstruction.paperOptimizer (V j) (B j) (aProj V j z) (bProj V j z) := by
    change WithLp.snd z j = _
    rw [hw]
    rfl
  have hr := BranchConstruction.paperOptimizer_terminal_source (V j) (B j) (aProj V j z) (u j) (bProj V j z)
  rw [← hwj, ← hprop] at hr
  have hcap := radialCap_fderiv_identity (by norm_num : (0 : ℝ) < 21) (bProj V j z) hb
  have hscore : ⟪stateProj V j z, v j⟫_ℝ = score V v j z := by
    rw [score, stateScore, radialCap_identity (by norm_num : (0 : ℝ) < 10) hs, real_inner_comm]
  change activationLoad (precedingScore V v j z) (stateScore (v j) (stateProj V j z)) = 1 at hL
  simp only [portDerivative, portOuterDerivative, inner_zero_right, inner_zero_left, map_zero,
    hcap, ContinuousLinearMap.id_apply, hL, mul_one, zero_add, add_zero, mul_zero, zero_sub,
    radialCap_identity (by norm_num : (0 : ℝ) < 10) hs, hscore]
  have hcomm : ⟪v j, dualProj V j z (Fin.last (m + 1))⟫_ℝ =
      ⟪dualProj V j z (Fin.last (m + 1)), v j⟫_ℝ := real_inner_comm _ _
  rw [hcomm]
  dsimp [EndpointConstants.endpointD]
  nlinarith only [hr]

end
end NCConcave16991.GlobalHard
