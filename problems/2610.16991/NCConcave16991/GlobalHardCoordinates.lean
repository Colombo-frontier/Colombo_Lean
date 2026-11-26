import NCConcave16991.GlobalHardConstruction

namespace NCConcave16991.GlobalHard
noncomputable section
open scoped InnerProductSpace
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
variable {M N : ℕ} (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)]
theorem stateProj_norm (j : Fin M) : ‖stateProj V j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound (stateProj V j) (by norm_num)
  intro z
  simp only [one_mul]
  change ‖WithLp.fst (WithLp.fst z j)‖ ≤ ‖z‖
  have hh := (WithLp.norm_fst_le (p := 2) (α := _) (β := _) (WithLp.fst z j)).trans
    ((PiLp.norm_apply_le (p := 2) (WithLp.fst z) j).trans (WithLp.norm_fst_le (p := 2) (α := _) (β := _) z))
  exact hh

theorem aProj_norm (j : Fin M) : ‖aProj V j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound (aProj V j) (by norm_num)
  intro z
  simp only [one_mul]
  change ‖WithLp.fst (WithLp.snd (WithLp.fst z j))‖ ≤ ‖z‖
  have hh := (WithLp.norm_fst_le (p := 2) (α := _) (β := _) (WithLp.snd (WithLp.fst z j))).trans
    ((WithLp.norm_snd_le (p := 2) (α := _) (β := _) (WithLp.fst z j)).trans
      ((PiLp.norm_apply_le (p := 2) (WithLp.fst z) j).trans (WithLp.norm_fst_le (p := 2) (α := _) (β := _) z)))
  exact hh

theorem bProj_norm (j : Fin M) : ‖bProj V j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound (bProj V j) (by norm_num)
  intro z
  simp only [one_mul]
  change ‖WithLp.snd (WithLp.snd (WithLp.fst z j))‖ ≤ ‖z‖
  have hh := (WithLp.norm_snd_le (p := 2) (α := _) (β := _) (WithLp.snd (WithLp.fst z j))).trans
    ((WithLp.norm_snd_le (p := 2) (α := _) (β := _) (WithLp.fst z j)).trans
      ((PiLp.norm_apply_le (p := 2) (WithLp.fst z) j).trans (WithLp.norm_fst_le (p := 2) (α := _) (β := _) z)))
  exact hh

theorem pipeProj_norm (j : Fin M) : ‖pipeProj V j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound (pipeProj V j) (by norm_num)
  intro z
  simp only [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hc := (WithLp.norm_snd_le (p := 2) (α := _) (β := _) (WithLp.fst z j)).trans
    (PiLp.norm_apply_le (p := 2) (WithLp.fst z) j)
  have hw := PiLp.norm_apply_le (p := 2) (WithLp.snd z) j
  have hc2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
  have hw2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
  change ‖WithLp.toLp 2 (connectorProj V j z, dualProj V j z)‖ ^ 2 ≤ ‖z‖ ^ 2
  rw [WithLp.prod_norm_sq_eq_of_L2]
  conv_rhs => rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖WithLp.snd (WithLp.fst z j)‖ ^ 2 + ‖WithLp.snd z j‖ ^ 2 ≤
    ‖WithLp.fst z‖ ^ 2 + ‖WithLp.snd z‖ ^ 2
  exact add_le_add hc2 hw2


end
end NCConcave16991.GlobalHard
