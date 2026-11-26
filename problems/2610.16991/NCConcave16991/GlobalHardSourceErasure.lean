import NCConcave16991.GlobalHardSupport

/-! # Exact prefix source erasure of the complete component first jet -/

namespace NCConcave16991.GlobalHard

noncomputable section

open LocalizationScalar
open scoped BigOperators InnerProductSpace Topology

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4

variable {A E : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem outerStage_flat_current (u : A) (v : E) (previous : ℝ) (s : E) (a : A) (b : E)
    (ht : stateScore v s ≤ deltaGate) :
    outerStage u v previous s a b = outerStage u 0 previous s a b := by
  have hg : gate (stateScore v s) = 0 := gate_zero (ht.trans (by norm_num [deltaGate]))
  have hh := activation_zero ht
  have hp := statePotential_left (ht.trans (by norm_num [deltaGate] : deltaGate ≤ 1 / 10))
  have hz : stateScore (0 : E) s = 0 := by simp [stateScore]
  simp only [outerStage, entrance, exit, activationLoad, stateCoupling, statePenalty, activationSq, hg, hh, hp, hz,
    gate_zero (by norm_num : (0 : ℝ) ≤ 1 / 5), activation_zero deltaGate_pos.le,
    statePotential_left (by norm_num : (0 : ℝ) ≤ 1 / 10)]

theorem outerStage_flat_both (u : A) (v : E) (previous : ℝ) (s : E) (a : A) (b : E)
    (hp : gate previous = 0) (ht : stateScore v s ≤ deltaGate) :
    outerStage u v previous s a b = gamma / 2 * ‖s‖ ^ 2 := by
  rw [outerStage_flat_current u v previous s a b ht]
  have hz : stateScore (0 : E) s = 0 := by simp [stateScore]
  simp [outerStage, entrance, exit, activationLoad, stateCoupling, statePenalty, activationSq, hp, hz,
    gate_zero (by norm_num : (0 : ℝ) ≤ 1 / 5), activation_zero deltaGate_pos.le,
    statePotential_left (by norm_num : (0 : ℝ) ≤ 1 / 10)]

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {M N : ℕ} (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)]

def knownIncoming (r : ℕ) (u : ∀ j, V j 0) (j : Fin M) : V j 0 := if j.val ≤ r then u j else 0
def knownTerminal (r : ℕ) (v : ∀ j, V j (Fin.last N)) (j : Fin M) : V j (Fin.last N) :=
  if j.val < r then v j else 0

theorem precedingScore_known_of_le (r : ℕ) (v : ∀ j, V j (Fin.last N)) (j : Fin M)
    (hj : j.val ≤ r) (z : Joint V) :
    precedingScore V (knownTerminal V r v) j z = precedingScore V v j z := by
  by_cases hj0 : j.val = 0
  · rw [precedingScore_of_zero V _ j hj0, precedingScore_of_zero V _ j hj0]
  · rw [precedingScore_of_positive V _ j hj0, precedingScore_of_positive V _ j hj0]
    have hp : (predecessor j hj0).val < r := by dsimp [predecessor]; omega
    simp only [knownTerminal, if_pos hp]

theorem precedingScore_known_of_gt (r : ℕ) (v : ∀ j, V j (Fin.last N)) (j : Fin M)
    (hj : r < j.val) (z : Joint V) : precedingScore V (knownTerminal V r v) j z = 0 := by
  have hj0 : j.val ≠ 0 := by omega
  rw [precedingScore_of_positive V _ j hj0]
  have hp : ¬(predecessor j hj0).val < r := by dsimp [predecessor]; omega
  simp [knownTerminal, hp, stateScore]

theorem outerStage_prefix_erasure (r : ℕ) (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))
    (z : Joint V) (hflat : ∀ j : Fin M, r ≤ j.val → stateScore (v j) (stateProj V j z) ≤ deltaGate)
    (j : Fin M) :
    outerStage (u j) (v j) (precedingScore V v j z) (stateProj V j z) (aProj V j z) (bProj V j z) =
      outerStage (knownIncoming V r u j) (knownTerminal V r v j)
        (precedingScore V (knownTerminal V r v) j z) (stateProj V j z) (aProj V j z) (bProj V j z) := by
  by_cases hj : j.val < r
  · have hj' : j.val ≤ r := hj.le
    rw [precedingScore_known_of_le V r v j hj']
    simp only [knownIncoming, knownTerminal, if_pos hj, if_pos hj']
  · have hcur := hflat j (le_of_not_gt hj)
    by_cases hjr : j.val ≤ r
    · rw [precedingScore_known_of_le V r v j hjr]
      simp only [knownIncoming, knownTerminal, if_pos hjr, if_neg hj]
      exact outerStage_flat_current _ _ _ _ _ _ hcur
    · have hgt : r < j.val := lt_of_not_ge hjr
      have hj0 : j.val ≠ 0 := by omega
      have hp : r ≤ (predecessor j hj0).val := by dsimp [predecessor]; omega
      have hprev : gate (precedingScore V v j z) = 0 := by
        rw [precedingScore_of_positive V v j hj0]
        exact gate_zero ((hflat _ hp).trans (by norm_num [deltaGate]))
      rw [outerStage_flat_both _ _ _ _ _ _ hprev hcur, precedingScore_known_of_gt V r v j hgt]
      simp only [knownTerminal, if_neg hj]
      symm
      apply outerStage_flat_both
      · exact gate_zero (by norm_num)
      · simp only [stateScore, inner_zero_left]
        exact deltaGate_pos.le

variable (B : ∀ j : Fin M, ∀ t : Fin N,
  BranchGeometry.BranchFamily (ι := ι) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))

theorem component_prefix_erasure (r : ℕ) (d q μ : ℝ) (i : ι) (z : Joint V)
    (hflat : ∀ j : Fin M, r ≤ j.val → stateScore (v j) (stateProj V j z) ≤ deltaGate) :
    component V B u v d q μ i z = component V B (knownIncoming V r u) (knownTerminal V r v) d q μ i z := by
  unfold component
  apply Finset.sum_congr rfl
  intro j _
  rw [outerStage_prefix_erasure V r u v z hflat j]

/-- Strict inactive scores give equality of the literal component functions
on an actual open neighborhood of the complete query point. -/
theorem component_prefix_eventuallyEq (r : ℕ) (d q μ : ℝ) (i : ι) (z : Joint V)
    (hflat : ∀ j : Fin M, r ≤ j.val → stateScore (v j) (stateProj V j z) < deltaGate) :
    component V B u v d q μ i =ᶠ[𝓝 z]
      component V B (knownIncoming V r u) (knownTerminal V r v) d q μ i := by
  have hj (j : Fin M) : ∀ᶠ x in 𝓝 z, r ≤ j.val → stateScore (v j) (stateProj V j x) ≤ deltaGate := by
    by_cases h : r ≤ j.val
    · have hc : Continuous (fun x : Joint V ↦ stateScore (v j) (stateProj V j x)) := (score_contDiff V v j).continuous
      have hn := (isOpen_lt hc continuous_const).mem_nhds (hflat j h)
      filter_upwards [hn] with x hx
      exact fun _ ↦ hx.le
    · filter_upwards [] with x
      exact fun hx ↦ False.elim (h hx)
  filter_upwards [Filter.eventually_all.2 hj] with x hx
  exact component_prefix_erasure V B u v r d q μ i x hx

/-- The entire value/full-gradient oracle answer is independent of all
unreleased suffix sources, without supplying a hidden source projection. -/
theorem component_prefix_firstJet (r : ℕ) (d q μ : ℝ) (i : ι) (z : Joint V)
    (hflat : ∀ j : Fin M, r ≤ j.val → stateScore (v j) (stateProj V j z) < deltaGate) :
    (component V B u v d q μ i z, gradient (component V B u v d q μ i) z) =
      (component V B (knownIncoming V r u) (knownTerminal V r v) d q μ i z,
        gradient (component V B (knownIncoming V r u) (knownTerminal V r v) d q μ i) z) := by
  exact Prod.ext (component_prefix_erasure V B u v r d q μ i z (fun j hj ↦ (hflat j hj).le))
    (component_prefix_eventuallyEq V B u v r d q μ i z hflat).gradient_eq

end

end NCConcave16991.GlobalHard
