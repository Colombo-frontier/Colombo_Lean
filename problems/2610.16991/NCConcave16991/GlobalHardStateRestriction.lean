import NCConcave16991.GlobalHardStateSection

/-! # The global component restricted to one literal state coordinate -/

namespace NCConcave16991.GlobalHard

noncomputable section
open LocalizationScalar LocalizationRadial
open scoped BigOperators InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 800000

variable {M N : ℕ} (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)]

def entryPair (u : ∀ j, V j 0) (z : Joint V) (j : Fin M) : ℝ :=
  ⟪u j, radialCap 21 (aProj V j z)⟫_ℝ

def outerAt (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N)) (z : Joint V) (j : Fin M) : ℝ :=
  outerStage (u j) (v j) (precedingScore V v j z) (stateProj V j z) (aProj V j z) (bProj V j z)

theorem outerAt_outgoing_form (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))
    (z : Joint V) (j : Fin M) :
    outerAt V u v z j = statePenalty (v j) (stateProj V j z) +
      outgoingScoreFunction (precedingScore V v j z) (score V v j z) (entryPair V u z j)
        (exitPair (stateProj V j z) (bProj V j z)) := by
  rw [outgoingScoreFunction_eq]
  dsimp [outerAt, outerStage, entrance, exit, activationLoad, stateCoupling, entryPair, exitPair, score]
  rw [real_inner_comm (radialCap 21 _) (radialCap 10 _)]
  ring

theorem outerAt_stateSection_self (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))
    (z : Joint V) (j : Fin M) (s : V j (Fin.last N)) :
    outerAt V u v (stateSection V z j s) j =
      outerStage (u j) (v j) (precedingScore V v j z) s (aProj V j z) (bProj V j z) := by
  simp only [outerAt, precedingScore_stateSection_self, stateProj_stateSection_same,
    aProj_stateSection, bProj_stateSection]

theorem outerAt_stateSection_other (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))
    (z : Joint V) (j k : Fin M) (hkj : k ≠ j) (hk : k.val ≠ j.val + 1) (s : V j (Fin.last N)) :
    outerAt V u v (stateSection V z j s) k = outerAt V u v z k := by
  simp only [outerAt, precedingScore_stateSection_other V v z j k hk,
    stateProj_stateSection_ne V z j k hkj, aProj_stateSection, bProj_stateSection]

theorem outerAt_stateSection_next_sub (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))
    (z : Joint V) (j k : Fin M) (hk : k.val = j.val + 1) (s : V j (Fin.last N)) :
    outerAt V u v (stateSection V z j s) k - outerAt V u v z k =
      outgoingScoreFunction (stateScore (v j) s) (score V v k z) (entryPair V u z k)
        (exitPair (stateProj V k z) (bProj V k z)) -
      outgoingScoreFunction (score V v j z) (score V v k z) (entryPair V u z k)
        (exitPair (stateProj V k z) (bProj V k z)) := by
  have hkj : k ≠ j := by intro he; subst k; omega
  have hprev : precedingScore V v k z = score V v j z := by
    have hk0 : k.val ≠ 0 := by omega
    have hp : predecessor k hk0 = j := by apply Fin.ext; dsimp [predecessor]; omega
    rw [precedingScore_of_positive V v k hk0, hp]
    rfl
  rw [outerAt_outgoing_form, outerAt_outgoing_form]
  simp only [precedingScore_stateSection_next V v z j k hk, hprev, score,
    stateProj_stateSection_ne V z j k hkj, entryPair, aProj_stateSection, bProj_stateSection]
  ring

private theorem sum_two_support {I : Type*} [Fintype I] [DecidableEq I]
    (a b : I) (hab : a ≠ b) (f : I → ℝ) (hf : ∀ k, k ≠ a → k ≠ b → f k = 0) :
    ∑ k, f k = f a + f b := by
  rw [← Finset.sum_erase_add (Finset.univ : Finset I) f (Finset.mem_univ b)]
  congr 1
  apply Finset.sum_eq_single a
  · intro k hk hka
    exact hf k hka (Finset.ne_of_mem_erase hk)
  · intro hnot
    exact False.elim (hnot (Finset.mem_erase.mpr ⟨hab, Finset.mem_univ a⟩))

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  (B : ∀ j : Fin M, ∀ t : Fin N,
    BranchGeometry.BranchFamily (ι := ι) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))

theorem component_stateSection_sub_eq_sum (d r μ : ℝ) (i : ι)
    (z : Joint V) (j : Fin M) (s : V j (Fin.last N)) :
    component V B u v d r μ i (stateSection V z j s) - component V B u v d r μ i z =
      ∑ k : Fin M, (outerAt V u v (stateSection V z j s) k - outerAt V u v z k) := by
  simp only [component, ← Finset.sum_sub_distrib, pipeProj_stateSection, outerAt]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem component_stateSection_sub_next (d r μ : ℝ) (i : ι) (z : Joint V)
    (j k : Fin M) (hk : k.val = j.val + 1) (s : V j (Fin.last N)) :
    component V B u v d r μ i (stateSection V z j s) - component V B u v d r μ i z =
      localStateObjective (v j) (bProj V j z) (precedingScore V v j z) (score V v k z)
        (entryPair V u z j) (entryPair V u z k) (exitPair (stateProj V k z) (bProj V k z)) s -
      localStateObjective (v j) (bProj V j z) (precedingScore V v j z) (score V v k z)
        (entryPair V u z j) (entryPair V u z k) (exitPair (stateProj V k z) (bProj V k z)) (stateProj V j z) := by
  rw [component_stateSection_sub_eq_sum]
  have hjk : j ≠ k := by intro he; subst k; omega
  rw [sum_two_support j k hjk]
  · rw [outerAt_stateSection_self, outerAt_stateSection_next_sub V u v z j k hk]
    rw [show entryPair V u z j = ⟪u j, radialCap 21 (aProj V j z)⟫_ℝ from rfl,
      localStateObjective_eq_outer, localStateObjective_eq_outer]
    dsimp [outerAt, score]
    ring
  · intro a haj hak
    have ha : a.val ≠ j.val + 1 := by
      intro he
      exact hak (Fin.ext (he.trans hk.symm))
    rw [outerAt_stateSection_other V u v z j a haj ha]
    ring

theorem component_stateSection_sub_last (d r μ : ℝ) (i : ι) (z : Joint V)
    (j : Fin M) (hj : ¬j.val + 1 < M) (s : V j (Fin.last N)) :
    component V B u v d r μ i (stateSection V z j s) - component V B u v d r μ i z =
      localStateObjective (v j) (bProj V j z) (precedingScore V v j z) 0
        (entryPair V u z j) 0 0 s -
      localStateObjective (v j) (bProj V j z) (precedingScore V v j z) 0
        (entryPair V u z j) 0 0 (stateProj V j z) := by
  rw [component_stateSection_sub_eq_sum, Finset.sum_eq_single j]
  · rw [outerAt_stateSection_self]
    rw [show entryPair V u z j = ⟪u j, radialCap 21 (aProj V j z)⟫_ℝ from rfl,
      localStateObjective_eq_outer, localStateObjective_eq_outer]
    simp [outgoingScoreFunction, outgoingScoreCoefficient, gate_zero (by norm_num : (0 : ℝ) ≤ 1 / 5), outerAt]
  · intro k _ hkj
    rw [outerAt_stateSection_other V u v z j k hkj (by omega)]
    ring
  · simp

/-- The actual neighboring data, with zero outgoing terms at the last stage. -/
def stateObjectiveAt (z : Joint V) (j : Fin M) : V j (Fin.last N) → ℝ :=
  if hj : j.val + 1 < M then
    let k : Fin M := ⟨j.val + 1, hj⟩
    localStateObjective (v j) (bProj V j z) (precedingScore V v j z) (score V v k z)
      (entryPair V u z j) (entryPair V u z k) (exitPair (stateProj V k z) (bProj V k z))
  else
    localStateObjective (v j) (bProj V j z) (precedingScore V v j z) 0 (entryPair V u z j) 0 0

theorem component_stateSection_sub (d r μ : ℝ) (i : ι) (z : Joint V)
    (j : Fin M) (s : V j (Fin.last N)) :
    component V B u v d r μ i (stateSection V z j s) - component V B u v d r μ i z =
      stateObjectiveAt V u v z j s - stateObjectiveAt V u v z j (stateProj V j z) := by
  by_cases hj : j.val + 1 < M
  · simpa [stateObjectiveAt, hj] using component_stateSection_sub_next V B u v d r μ i z j ⟨j.val + 1, hj⟩ rfl s
  · simpa [stateObjectiveAt, hj] using component_stateSection_sub_last V B u v d r μ i z j hj s

/-- Averaging changes none of the state-coordinate variation. -/
theorem average_stateSection_sub (d r μ : ℝ) (z : Joint V)
    (j : Fin M) (s : V j (Fin.last N)) :
    average V B u v d r μ (stateSection V z j s) - average V B u v d r μ z =
      stateObjectiveAt V u v z j s - stateObjectiveAt V u v z j (stateProj V j z) := by
  unfold average
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simp_rw [component_stateSection_sub]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem average_stateSection_eq (d r μ : ℝ) (z : Joint V)
    (j : Fin M) (s : V j (Fin.last N)) :
    average V B u v d r μ (stateSection V z j s) =
      stateObjectiveAt V u v z j s +
        (average V B u v d r μ z - stateObjectiveAt V u v z j (stateProj V j z)) := by
  have hh := average_stateSection_sub V B u v d r μ z j s
  linarith

end
end NCConcave16991.GlobalHard
