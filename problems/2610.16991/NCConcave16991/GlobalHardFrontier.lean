import NCConcave16991.GlobalHardStateTransport

/-! # The unique high-prefix/low-suffix frontier of the literal construction -/

namespace NCConcave16991.GlobalHard
noncomputable section
open LocalizationScalar
open scoped InnerProductSpace

private theorem scalar_frontier {M : ℕ} (q : Fin M → ℝ)
    (hclass : ∀ j, (-1 / 10 < q j ∧ q j ≤ 1 / 5) ∨ 1 ≤ q j)
    (hno : ∀ j k, k.val = j.val + 1 → -1 / 10 < q j → q j ≤ 1 / 5 → 1 ≤ q k → False)
    (hex : ∃ j, q j ≤ 1 / 5) :
    ∃ f : Fin M, (∀ j, j.val < f.val → 1 ≤ q j) ∧
      (∀ j, f.val ≤ j.val → -1 / 10 < q j ∧ q j ≤ 1 / 5) := by
  classical
  let S : Finset (Fin M) := Finset.univ.filter (fun j ↦ q j ≤ 1 / 5)
  have hS : S.Nonempty := by
    obtain ⟨j, hj⟩ := hex
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  let f := S.min' hS
  have hfmem : f ∈ S := Finset.min'_mem S hS
  have hfupper : q f ≤ 1 / 5 := (Finset.mem_filter.mp hfmem).2
  have hflow : -1 / 10 < q f ∧ q f ≤ 1 / 5 := by
    rcases hclass f with h | h
    · exact h
    · linarith
  refine ⟨f, ?_, ?_⟩
  · intro j hj
    rcases hclass j with hl | hh
    · have hjmem : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hl.2⟩
      have hm : f ≤ j := Finset.min'_le S j hjmem
      have hmv : f.val ≤ j.val := hm
      omega
    · exact hh
  · have htail : ∀ n, f.val ≤ n → ∀ hn : n < M,
        -1 / 10 < q ⟨n, hn⟩ ∧ q ⟨n, hn⟩ ≤ 1 / 5 := by
      intro n hfn
      apply Nat.le_induction (P := fun a _ ↦ ∀ ha : a < M,
        -1 / 10 < q ⟨a, ha⟩ ∧ q ⟨a, ha⟩ ≤ 1 / 5) ?_ ?_ n hfn
      · intro hf
        exact hflow
      · intro a ha ih hanext
        have haM : a < M := by omega
        rcases hclass ⟨a + 1, hanext⟩ with hl | hh
        · exact hl
        · exact False.elim (hno ⟨a, haM⟩ ⟨a + 1, hanext⟩ rfl (ih haM).1 (ih haM).2 hh)
    intro j hj
    exact htail j.val hj j.isLt

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {M N : ℕ} (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)]
variable (B : ∀ j : Fin M, ∀ t : Fin N,
    BranchGeometry.BranchFamily (ι := ι) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))

theorem average_frontier (d r μ : ℝ) (z : Joint V)
    (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1)
    (hg : ‖gradient (primalAverageSection V B u v d r μ (WithLp.snd z)) (WithLp.fst z)‖ ≤ 1 / 20)
    (hex : ∃ j, score V v j z < 1) :
    ∃ f : Fin M, (∀ j, j.val < f.val → 1 ≤ score V v j z) ∧
      (∀ j, f.val ≤ j.val → -1 / 10 < score V v j z ∧ score V v j z ≤ 1 / 5) := by
  have hc := average_state_classification V B u v d r μ z hu hv hg
  apply scalar_frontier (score V v · z) hc
  · exact fun j k hk hl ht hn ↦ average_no_low_high V B u v d r μ z hu hv hg j k hk hl ht hn
  · obtain ⟨j, hj⟩ := hex
    rcases hc j with hl | hh
    · exact ⟨j, hl.2⟩
    · linarith

theorem activationLoad_zero_before_frontier (z : Joint V) (f : Fin M)
    (hhigh : ∀ j, j.val < f.val → 1 ≤ score V v j z)
    (j : Fin M) (hj : j.val < f.val) :
    activationLoad (precedingScore V v j z) (score V v j z) = 0 := by
  simp [activationLoad, gate_one (hhigh j hj)]

theorem activationLoad_zero_after_frontier (z : Joint V) (f : Fin M)
    (hlow : ∀ j, f.val ≤ j.val → score V v j z ≤ 1 / 5)
    (j : Fin M) (hj : f.val < j.val) :
    activationLoad (precedingScore V v j z) (score V v j z) = 0 := by
  have hj0 : j.val ≠ 0 := by omega
  have hp : f.val ≤ (predecessor j hj0).val := by dsimp [predecessor]; omega
  rw [precedingScore_of_positive V v j hj0]
  have hgate : gate (stateScore (v (predecessor j hj0)) (stateProj V (predecessor j hj0) z)) = 0 :=
    gate_zero (hlow _ hp)
  simp only [activationLoad, hgate, zero_mul]

theorem activationLoad_frontier (z : Joint V) (f : Fin M)
    (hhigh : ∀ j, j.val < f.val → 1 ≤ score V v j z)
    (hlow : score V v f z ≤ 1 / 5) :
    activationLoad (precedingScore V v f z) (score V v f z) = 1 := by
  have hprev : gate (precedingScore V v f z) = 1 := by
    by_cases hf : f.val = 0
    · rw [precedingScore_of_zero V v f hf]
      exact gate_one le_rfl
    · rw [precedingScore_of_positive V v f hf]
      apply gate_one
      exact hhigh _ (by dsimp [predecessor]; omega)
  simp [activationLoad, hprev, gate_zero hlow]

end
end NCConcave16991.GlobalHard
