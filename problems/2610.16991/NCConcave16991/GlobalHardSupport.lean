import NCConcave16991.GlobalHardBlocks

/-! # Formula-enforced local support of each literal global component -/

namespace NCConcave16991.GlobalHard

noncomputable section

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {M N : ℕ} (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)]

def predecessor (j : Fin M) (hj : j.val ≠ 0) : Fin M := ⟨j.val - 1, by omega⟩

theorem precedingScore_of_zero (v : ∀ j, V j (Fin.last N)) (j : Fin M)
    (hj : j.val = 0) (z : Joint V) : precedingScore V v j z = 1 := by
  have he : j.castSucc = 0 := Fin.ext hj
  simp [precedingScore, he]

theorem precedingScore_of_positive (v : ∀ j, V j (Fin.last N)) (j : Fin M)
    (hj : j.val ≠ 0) (z : Joint V) :
    precedingScore V v j z = stateScore (v (predecessor j hj)) (stateProj V (predecessor j hj) z) := by
  have he : j.castSucc = (predecessor j hj).succ := by
    apply Fin.ext
    simp only [Fin.val_castSucc, Fin.val_succ, predecessor]
    omega
  simp only [precedingScore, he, Fin.cases_succ, score]

theorem primal_regroup_mask (I : Finset (Fin M ⊕ Fin M)) (j : Fin M)
    (hj : Sum.inl j ∈ I) (z : Blocks V) :
    WithLp.fst (regroup V (HessianOverlap.blockProjection I z)) j = WithLp.fst (regroup V z) j := by
  change (if Sum.inl j ∈ I then z (Sum.inl j) else 0) = z (Sum.inl j)
  rw [if_pos hj]

theorem dual_regroup_mask (I : Finset (Fin M ⊕ Fin M)) (j : Fin M)
    (hj : Sum.inr j ∈ I) (z : Blocks V) :
    WithLp.snd (regroup V (HessianOverlap.blockProjection I z)) j = WithLp.snd (regroup V z) j := by
  change (if Sum.inr j ∈ I then z (Sum.inr j) else 0) = z (Sum.inr j)
  rw [if_pos hj]

theorem stateProj_regroup_mask (I : Finset (Fin M ⊕ Fin M)) (j : Fin M)
    (hj : Sum.inl j ∈ I) (z : Blocks V) :
    stateProj V j (regroup V (HessianOverlap.blockProjection I z)) = stateProj V j (regroup V z) := by
  change WithLp.fst (WithLp.fst (regroup V (HessianOverlap.blockProjection I z)) j) = _
  rw [primal_regroup_mask V I j hj z]
  rfl

theorem aProj_regroup_mask (I : Finset (Fin M ⊕ Fin M)) (j : Fin M)
    (hj : Sum.inl j ∈ I) (z : Blocks V) :
    aProj V j (regroup V (HessianOverlap.blockProjection I z)) = aProj V j (regroup V z) := by
  change WithLp.fst (WithLp.snd (WithLp.fst (regroup V (HessianOverlap.blockProjection I z)) j)) = _
  rw [primal_regroup_mask V I j hj z]
  rfl

theorem bProj_regroup_mask (I : Finset (Fin M ⊕ Fin M)) (j : Fin M)
    (hj : Sum.inl j ∈ I) (z : Blocks V) :
    bProj V j (regroup V (HessianOverlap.blockProjection I z)) = bProj V j (regroup V z) := by
  change WithLp.snd (WithLp.snd (WithLp.fst (regroup V (HessianOverlap.blockProjection I z)) j)) = _
  rw [primal_regroup_mask V I j hj z]
  rfl

theorem pipeProj_regroup_mask (I : Finset (Fin M ⊕ Fin M)) (j : Fin M)
    (hp : Sum.inl j ∈ I) (hd : Sum.inr j ∈ I) (z : Blocks V) :
    pipeProj V j (regroup V (HessianOverlap.blockProjection I z)) = pipeProj V j (regroup V z) := by
  change WithLp.toLp 2 (WithLp.snd (WithLp.fst (regroup V (HessianOverlap.blockProjection I z)) j),
    WithLp.snd (regroup V (HessianOverlap.blockProjection I z)) j) = _
  rw [primal_regroup_mask V I j hp z, dual_regroup_mask V I j hd z]
  rfl

theorem precedingScore_regroup_support (v : ∀ j, V j (Fin.last N)) (j : Fin M) (z : Blocks V) :
    precedingScore V v j (regroup V (HessianOverlap.blockProjection (support j) z)) =
      precedingScore V v j (regroup V z) := by
  by_cases hj : j.val = 0
  · rw [precedingScore_of_zero V v j hj, precedingScore_of_zero V v j hj]
  · rw [precedingScore_of_positive V v j hj, precedingScore_of_positive V v j hj]
    rw [stateProj_regroup_mask V (support j) (predecessor j hj) _ z]
    rw [mem_support_inl]
    right
    dsimp [predecessor]
    omega

variable (B : ∀ j : Fin M, ∀ t : Fin N,
  BranchGeometry.BranchFamily (ι := ι) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))

def stageComponent (d r μ : ℝ) (i : ι) (j : Fin M) (z : Joint V) : ℝ :=
  PipeSmoothness.component (B j) d r μ i (pipeProj V j z) +
    outerStage (u j) (v j) (precedingScore V v j z) (stateProj V j z) (aProj V j z) (bProj V j z)

theorem stageComponent_regroup_support (d r μ : ℝ) (i : ι) (j : Fin M) (z : Blocks V) :
    stageComponent V B u v d r μ i j (regroup V (HessianOverlap.blockProjection (support j) z)) =
      stageComponent V B u v d r μ i j (regroup V z) := by
  have hp : Sum.inl j ∈ support j := (mem_support_inl j j).mpr (Or.inl rfl)
  have hd : Sum.inr j ∈ support j := (mem_support_inr j j).mpr rfl
  simp only [stageComponent, pipeProj_regroup_mask V (support j) j hp hd z,
    precedingScore_regroup_support V v j z, stateProj_regroup_mask V (support j) j hp z,
    aProj_regroup_mask V (support j) j hp z, bProj_regroup_mask V (support j) j hp z]

theorem component_eq_supported_sum (d r μ : ℝ) (i : ι) (z : Blocks V) :
    component V B u v d r μ i (regroup V z) =
      ∑ j, stageComponent V B u v d r μ i j (regroup V (HessianOverlap.blockProjection (support j) z)) := by
  simp only [stageComponent_regroup_support]
  rfl

end

end NCConcave16991.GlobalHard
