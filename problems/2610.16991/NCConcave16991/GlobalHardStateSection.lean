import NCConcave16991.GlobalHardSupport
import NCConcave16991.GlobalHardStateGradient

/-! # Actual affine sections through a single state coordinate -/

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

def primalStateInjection (j : Fin M) : V j (Fin.last N) →ₗᵢ[ℝ] Primal V where
  toFun s := PiLp.single 2 j (WithLp.toLp 2 (s, 0))
  map_add' := by
    intro s t
    ext k
    by_cases hk : k = j
    · subst k; simp; apply WithLp.ofLp_injective 2; change (s + t, (0 : PipeSmoothness.Connectors (V j))) = (s, 0) + (t, 0); simp
    · simp [PiLp.single_eq_of_ne 2 hk]
  map_smul' := by
    intro c s
    ext k
    by_cases hk : k = j
    · subst k; simp; apply WithLp.ofLp_injective 2; change (c • s, (0 : PipeSmoothness.Connectors (V j))) = c • (s, 0); simp
    · simp [PiLp.single_eq_of_ne 2 hk]
  norm_map' s := by
    change ‖PiLp.single 2 (β := PrimalStage V) j (WithLp.toLp 2 (s, 0))‖ = ‖s‖
    rw [PiLp.norm_single]
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp

def stateInjection (j : Fin M) : V j (Fin.last N) →L[ℝ] Joint V :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    ((primalStateInjection V j).toContinuousLinearMap.prod (0 : V j (Fin.last N) →L[ℝ] Dual V))

theorem stateInjection_apply (j : Fin M) (s : V j (Fin.last N)) :
    stateInjection V j s = WithLp.toLp 2 (primalStateInjection V j s, 0) := rfl

theorem stateInjection_norm (j : Fin M) (s : V j (Fin.last N)) : ‖stateInjection V j s‖ = ‖s‖ := by
  rw [stateInjection_apply]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp

theorem stateProj_stateInjection_same (j : Fin M) (s : V j (Fin.last N)) :
    stateProj V j (stateInjection V j s) = s := by
  change WithLp.fst (PiLp.single 2 (β := PrimalStage V) j (WithLp.toLp 2 (s, 0)) j) = s
  simp

theorem stateProj_stateInjection_ne (j k : Fin M) (h : k ≠ j) (s : V j (Fin.last N)) :
    stateProj V k (stateInjection V j s) = 0 := by
  change WithLp.fst (PiLp.single 2 (β := PrimalStage V) j (WithLp.toLp 2 (s, 0)) k) = 0
  simp [PiLp.single_eq_of_ne 2 h]

theorem connectorProj_stateInjection (j k : Fin M) (s : V j (Fin.last N)) :
    connectorProj V k (stateInjection V j s) = 0 := by
  change WithLp.snd (PiLp.single 2 (β := PrimalStage V) j (WithLp.toLp 2 (s, 0)) k) = 0
  by_cases h : k = j
  · subst k; simp
  · simp [PiLp.single_eq_of_ne 2 h]

theorem dualProj_stateInjection (j k : Fin M) (s : V j (Fin.last N)) :
    dualProj V k (stateInjection V j s) = 0 := by rfl

theorem pipeProj_stateInjection (j k : Fin M) (s : V j (Fin.last N)) :
    pipeProj V k (stateInjection V j s) = 0 := by
  change WithLp.toLp 2 (connectorProj V k (stateInjection V j s),
    dualProj V k (stateInjection V j s)) = 0
  rw [connectorProj_stateInjection, dualProj_stateInjection]
  rfl

theorem aProj_stateInjection (j k : Fin M) (s : V j (Fin.last N)) :
    aProj V k (stateInjection V j s) = 0 := by
  simp [aProj, pipeProj_stateInjection]

theorem bProj_stateInjection (j k : Fin M) (s : V j (Fin.last N)) :
    bProj V k (stateInjection V j s) = 0 := by
  simp [bProj, pipeProj_stateInjection]

def stateSection (z : Joint V) (j : Fin M) (s : V j (Fin.last N)) : Joint V :=
  z + stateInjection V j (s - stateProj V j z)

theorem stateSection_base (z : Joint V) (j : Fin M) : stateSection V z j (stateProj V j z) = z := by
  simp [stateSection]

theorem stateSection_hasFDerivAt (z : Joint V) (j : Fin M) (s : V j (Fin.last N)) :
    HasFDerivAt (stateSection V z j) (stateInjection V j) s := by
  exact (((stateInjection V j).hasFDerivAt.comp s
    ((hasFDerivAt_id s).sub_const (stateProj V j z))).const_add z).congr_fderiv (by simp)

theorem stateProj_stateSection_same (z : Joint V) (j : Fin M) (s : V j (Fin.last N)) :
    stateProj V j (stateSection V z j s) = s := by
  simp only [stateSection, map_add, stateProj_stateInjection_same]
  abel

theorem stateProj_stateSection_ne (z : Joint V) (j k : Fin M) (h : k ≠ j) (s : V j (Fin.last N)) :
    stateProj V k (stateSection V z j s) = stateProj V k z := by
  simp [stateSection, stateProj_stateInjection_ne V j k h]

theorem pipeProj_stateSection (z : Joint V) (j k : Fin M) (s : V j (Fin.last N)) :
    pipeProj V k (stateSection V z j s) = pipeProj V k z := by
  simp [stateSection, pipeProj_stateInjection]

theorem aProj_stateSection (z : Joint V) (j k : Fin M) (s : V j (Fin.last N)) :
    aProj V k (stateSection V z j s) = aProj V k z := by
  simp [stateSection, aProj_stateInjection]

theorem bProj_stateSection (z : Joint V) (j k : Fin M) (s : V j (Fin.last N)) :
    bProj V k (stateSection V z j s) = bProj V k z := by
  simp [stateSection, bProj_stateInjection]

theorem precedingScore_stateSection_self (v : ∀ j, V j (Fin.last N))
    (z : Joint V) (j : Fin M) (s : V j (Fin.last N)) :
    precedingScore V v j (stateSection V z j s) = precedingScore V v j z := by
  by_cases h : j.val = 0
  · rw [precedingScore_of_zero V v j h, precedingScore_of_zero V v j h]
  · rw [precedingScore_of_positive V v j h, precedingScore_of_positive V v j h,
      stateProj_stateSection_ne]
    intro he
    have hv := congrArg Fin.val he
    dsimp [predecessor] at hv
    omega

theorem precedingScore_stateSection_other (v : ∀ j, V j (Fin.last N))
    (z : Joint V) (j k : Fin M) (h : k.val ≠ j.val + 1) (s : V j (Fin.last N)) :
    precedingScore V v k (stateSection V z j s) = precedingScore V v k z := by
  by_cases hk : k.val = 0
  · rw [precedingScore_of_zero V v k hk, precedingScore_of_zero V v k hk]
  · rw [precedingScore_of_positive V v k hk, precedingScore_of_positive V v k hk,
      stateProj_stateSection_ne]
    intro he
    have hv := congrArg Fin.val he
    dsimp [predecessor] at hv
    omega

theorem precedingScore_stateSection_next (v : ∀ j, V j (Fin.last N))
    (z : Joint V) (j k : Fin M) (h : k.val = j.val + 1) (s : V j (Fin.last N)) :
    precedingScore V v k (stateSection V z j s) = stateScore (v j) s := by
  have hk : k.val ≠ 0 := by omega
  have he : predecessor k hk = j := by apply Fin.ext; dsimp [predecessor]; omega
  rw [precedingScore_of_positive V v k hk, he, stateProj_stateSection_same]

end
end NCConcave16991.GlobalHard
