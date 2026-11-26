import NCConcave16991.GlobalHardTerminalPorts
import NCConcave16991.GlobalHardTerminalState
import NCConcave16991.BranchAccounting

/-! # Actual small-primal-gradient witnesses have high terminal scores -/

namespace NCConcave16991.GlobalHard
noncomputable section
open Set
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

/-- The source's terminal certificate follows from the literal finite-sum
formula and an actual maximizing multiplier. No desired gradient, connector,
dual-interiority or eliminated-value formula is assumed. -/
theorem maximizing_small_primal_gradient_all_high (z : Joint V)
    (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1)
    (hprop : ∀ j, v j = BranchConstruction.terminalTransport (V j) (B j) (u j))
    (hg : ‖gradient (primalAverageSection V B u v (EndpointConstants.endpointD m)
      (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
      (1 / ((m : ℝ) + 2) ^ 2) (WithLp.snd z)) (WithLp.fst z)‖ ≤ 1 / 20)
    (hw : WithLp.snd z ∈ Metric.closedBall 0 (publicDualRadius (Fintype.card ι) (m + 2)))
    (hmax : IsMaxOn (fun w ↦ average V B u v (EndpointConstants.endpointD m)
      (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
      (1 / ((m : ℝ) + 2) ^ 2) (atDual V (WithLp.fst z) w))
      (Metric.closedBall 0 (publicDualRadius (Fintype.card ι) (m + 2))) (WithLp.snd z)) :
    ∀ j, 1 ≤ score V v j z := by
  intro j
  by_contra hj
  have hex : ∃ k, score V v k z < 1 := ⟨j, lt_of_not_ge hj⟩
  obtain ⟨hc, hopt⟩ := paper_maximizer_eq_optimizer_of_not_all_high V B u v z hu hv hg hex hw hmax
  obtain ⟨f, hhigh, hlow⟩ := average_frontier V B u v (EndpointConstants.endpointD m)
    (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
    (1 / ((m : ℝ) + 2) ^ 2) z hu hv hg hex
  have ha : ‖aProj V f z‖ ≤ 21 := by have hh := (ports_norm_le_connectorTuple V z f).1.trans hc; linarith
  have hb : ‖bProj V f z‖ ≤ 21 := by have hh := (ports_norm_le_connectorTuple V z f).2.trans hc; linarith
  have hs := average_low_state_norm V B u v (EndpointConstants.endpointD m)
    (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
    (1 / ((m : ℝ) + 2) ^ 2) z hu hv hg f (hlow f le_rfl).1 (hlow f le_rfl).2
  have hs10 : ‖stateProj V f z‖ ≤ 10 := by linarith
  have hL := activationLoad_frontier V v z f hhigh (hlow f le_rfl).2
  let ga := portDerivative (u f) (v f) (precedingScore V v f z) (stateProj V f z) (EndpointConstants.endpointD m)
    (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
    (dualProj V f z 0) (dualProj V f z (Fin.last (m + 1))) (aProj V f z) (bProj V f z) (u f) 0
  let gb := portDerivative (u f) (v f) (precedingScore V v f z) (stateProj V f z) (EndpointConstants.endpointD m)
    (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
    (dualProj V f z 0) (dualProj V f z (Fin.last (m + 1))) (aProj V f z) (bProj V f z) 0 (v f)
  have hga := portDerivative_abs_le_primalGradient V B u v (EndpointConstants.endpointD m)
    (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
    (1 / ((m : ℝ) + 2) ^ 2) z f (WithLp.toLp 2 (u f, 0))
  have hgb := portDerivative_abs_le_primalGradient V B u v (EndpointConstants.endpointD m)
    (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
    (1 / ((m : ℝ) + 2) ^ 2) z f (WithLp.toLp 2 (0, v f))
  have hna : ‖(WithLp.toLp 2 (u f, (0 : V f (Fin.last (m + 1)))))‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp [hu f]
  have hnb : ‖(WithLp.toLp 2 ((0 : V f 0), v f))‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp [hv f]
  rw [hna, mul_one] at hga
  rw [hnb, mul_one] at hgb
  have hga' : |ga| ≤ 1 / 20 := hga.trans hg
  have hgb' : |gb| ≤ 1 / 20 := hgb.trans hg
  have heqa := portDerivative_left_at_optimizer V B u v z f (hu f) (hprop f) hopt ha hL
  have heqb := portDerivative_right_at_optimizer V B u v z f (hprop f) hopt hb hs10 hL
  have hstate := average_frontier_state_pressure V B u v (EndpointConstants.endpointD m)
    (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
    (1 / ((m : ℝ) + 2) ^ 2) z hu hv hg f hhigh hlow hb
  exact BranchAccounting.terminal_scalar_contradiction ⟪aProj V f z, u f⟫_ℝ ⟪bProj V f z, v f⟫_ℝ
    (score V v f z) ga gb (netStateDerivative (score V v f z)) (by linarith [(hlow f le_rfl).1]) hga' hgb'
    heqa heqb (netStateDerivative_upper _) hstate

end
end NCConcave16991.GlobalHard
