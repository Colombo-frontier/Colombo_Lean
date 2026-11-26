import NCConcave16991.GlobalHardFrontier

/-! # Actual frontier state-pressure equation -/

namespace NCConcave16991.GlobalHard
noncomputable section
open LocalizationScalar LocalizationRadial LocalizationHessian
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 800000

theorem localStateObjective_frontier_pressure {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (v b : E) (hv : ‖v‖ = 1)
    (previous next entry nextEntry nextExit : ℝ) (s : E)
    (hs : ‖s‖ ≤ 10) (hb : ‖b‖ ≤ 21) (ht : stateScore v s ≤ 1 / 5) (hn : next ≤ 1 / 5)
    (hL : activationLoad previous (stateScore v s) = 1)
    (hg : ‖gradient (localStateObjective v b previous next entry nextEntry nextExit) s‖ ≤ 1 / 20) :
    |netStateDerivative (stateScore v s) - ⟪b, v⟫_ℝ| ≤ 1 / 20 := by
  have hd := localStateDerivative_abs_le_gradient v b previous next entry nextEntry nextExit s v
  rw [hv, mul_one] at hd
  have heq := localStateDerivative_source_eq v b hv previous next entry nextEntry nextExit s hs
  rw [incomingScoreDerivative_inactive _ _ _ _ ht, outgoingScoreDerivative_inactive _ _ _ _ ht,
    gate_zero hn, hL, radialCap_identity (by norm_num : (0 : ℝ) < 21) hb] at heq
  simp only [mul_zero, zero_mul, add_zero, one_mul] at heq
  rw [heq] at hd
  exact hd.trans hg

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {M N : ℕ} (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)]
variable (B : ∀ j : Fin M, ∀ t : Fin N,
    BranchGeometry.BranchFamily (ι := ι) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))

theorem average_frontier_state_pressure (d r μ : ℝ) (z : Joint V)
    (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1)
    (hg : ‖gradient (primalAverageSection V B u v d r μ (WithLp.snd z)) (WithLp.fst z)‖ ≤ 1 / 20)
    (f : Fin M) (hhigh : ∀ j, j.val < f.val → 1 ≤ score V v j z)
    (hlow : ∀ j, f.val ≤ j.val → -1 / 10 < score V v j z ∧ score V v j z ≤ 1 / 5)
    (hb : ‖bProj V f z‖ ≤ 21) :
    |netStateDerivative (score V v f z) - ⟪bProj V f z, v f⟫_ℝ| ≤ 1 / 20 := by
  have hs := average_low_state_norm V B u v d r μ z hu hv hg f (hlow f le_rfl).1 (hlow f le_rfl).2
  have hs10 : ‖stateProj V f z‖ ≤ 10 := by linarith
  have hL := activationLoad_frontier V v z f hhigh (hlow f le_rfl).2
  have hgrad := (stateObjectiveAt_gradient_le V B u v d r μ z f).trans hg
  by_cases hf : f.val + 1 < M
  · let k : Fin M := ⟨f.val + 1, hf⟩
    have hn := (hlow k (by dsimp [k]; omega)).2
    simp only [stateObjectiveAt, dif_pos hf] at hgrad
    exact localStateObjective_frontier_pressure (v f) (bProj V f z) (hv f)
      (precedingScore V v f z) (score V v k z) (entryPair V u z f) (entryPair V u z k)
      (exitPair (stateProj V k z) (bProj V k z)) (stateProj V f z)
      hs10 hb (hlow f le_rfl).2 hn hL hgrad
  · simp only [stateObjectiveAt, dif_neg hf] at hgrad
    exact localStateObjective_frontier_pressure (v f) (bProj V f z) (hv f)
      (precedingScore V v f z) 0 (entryPair V u z f) 0 0 (stateProj V f z)
      hs10 hb (hlow f le_rfl).2 (by norm_num) hL hgrad

end
end NCConcave16991.GlobalHard
