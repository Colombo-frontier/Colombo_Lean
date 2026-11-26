import NCConcave16991.ConeReferenceRelease

/-! # Upper support bounds for all row requests of the actual cone machine -/

open Set MeasureTheory

namespace NCConcave16991.Haar.ConeMachine

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n M : ℕ) (R : ℝ) (hR : 0 < R)

def RowAllowed (c : ConeCounter.State n) (ji : RowIndex n M) : Prop :=
  ji.1.val < c.1 ∨ ji.1.val = c.1 ∧ ji.2 ∈ c.2

theorem rowAllowed_step (c : ConeCounter.State n) (o : Option (Fin n)) (ji : RowIndex n M)
    (h : RowAllowed n M c ji) : RowAllowed n M (ConeCounter.step c o) ji := by
  cases o with
  | none => exact h
  | some i =>
      dsimp only [ConeCounter.step]
      split_ifs
      · left
        rcases h with h | ⟨h, _⟩ <;> omega
      · rcases h with h | ⟨h, hi⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, Finset.mem_insert_of_mem hi⟩

theorem paidUpdate_pendingStage (hn : 0 < n) (q : ℝ) (s : State E n M R hR) (a : E) :
    (paidUpdate E n M R hR hn q s a).pendingStage = s.pendingStage := by
  unfold paidUpdate paidQuery
  split_ifs <;> rfl

theorem paidUpdate_release_frontier (hn : 0 < n) (q : ℝ) (s : State E n M R hR) (a : E)
    (hs : s.pendingStage = s.progress.1)
    (hr : (paidUpdate E n M R hR hn q s a).release = true) :
    (paidUpdate E n M R hR hn q s a).pendingStage <
      (paidUpdate E n M R hR hn q s a).progress.1 := by
  unfold paidUpdate paidQuery at hr ⊢
  split_ifs at hr ⊢ <;> simp_all only [Bool.false_eq_true, shouldRelease, decide_eq_true_eq]
  simp only [ConeCounter.step, hr, ite_true]
  omega

theorem paidRequest_allowed (hn : 0 < n) (q : ℝ) (s : State E n M R hR) (a : E)
    (hp : s.phase.val = 1) (hs : s.pendingStage = s.progress.1)
    (ji : RowIndex n M) (he : request E n M R hR hn s = Sum.inr ji) :
    RowAllowed n M (paidUpdate E n M R hR hn q s a).progress ji := by
  cases hpend : s.pending with
  | inl x => simp [request, requestOfSummary, hp, pendingIndex, hpend] at he
  | inr o =>
      simp only [request, requestOfSummary, hp, one_ne_zero, ite_false, ite_true,
        pendingIndex, hpend, Sum.elim_inr, Option.elim_some] at he
      split_ifs at he with hvalid
      · injection he with he
        subst ji
        have hv : s.pendingStage % (M + 1) = s.progress.1 := by rw [Nat.mod_eq_of_lt hvalid, hs]
        simp only [paidUpdate, hpend, actionIsQuery, Sum.elim_inr, ite_true,
          paidQuery, hvalid, ite_true, actionQuery, RowAllowed, ConeCounter.step, hv]
        split_ifs
        · left; omega
        · right; exact ⟨rfl, Finset.mem_insert_self _ _⟩

theorem freeRequest_allowed (hn : 0 < n) (s : State E n M R hR)
    (hp0 : s.phase.val ≠ 0) (hp1 : s.phase.val ≠ 1)
    (hr : s.release = true → s.pendingStage < s.progress.1)
    (ji : RowIndex n M) (he : request E n M R hR hn s = Sum.inr ji) :
    RowAllowed n M s.progress ji := by
  simp only [request, requestOfSummary, hp0, hp1, ite_false] at he
  split_ifs at he with hrel hvalid
  · injection he with he
    subst ji
    left
    have hmod := Nat.mod_le s.pendingStage (M + 1)
    have hlt := hr hrel
    exact hmod.trans_lt hlt

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain E M R hR) (n := n) (dx := ConeProblem.primalDimension E M) Ω)

theorem cycle_request_allowed (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t k : ℕ) (hk : k < n + 2)
    (ji : RowIndex n M)
    (he : request E n M R hR hn (runWithRows E n M R hR P seed hn q rows ((n + 2) * t + k)) = Sum.inr ji) :
    RowAllowed n M (boundary E n M R hR P seed hn q rows (t + 1)).progress ji := by
  have hmeta := boundary_freeData_succ E n M R hR P seed hn q rows t
  have hprog := congrArg (fun d : FreeData E n M R hR ↦ d.2.1) hmeta
  dsimp only [freeData] at hprog
  by_cases hk0 : k = 0
  · subst k
    have hp := run_cycle_phase E n M R hR P seed hn q rows t 0 (by omega)
    simp only [request, requestOfSummary, hp, ite_true] at he
    cases he
  by_cases hk1 : k = 1
  · subst k
    rw [run_prepare] at he
    rw [hprog]
    apply paidRequest_allowed E n M R hR hn q _ _ _ rfl ji he
    rw [← run_prepare]
    exact run_cycle_phase E n M R hR P seed hn q rows t 1 (by omega)
  · have hkn : k - 2 < n := by omega
    have hidx : (n + 2) * t + k = (n + 2) * t + 2 + (k - 2) := by omega
    rw [hidx] at he
    change request E n M R hR hn (freeState E n M R hR P seed hn q rows t (k - 2)) = _ at he
    have hfree := run_freeData E n M R hR P seed hn q rows t (k - 2) hkn.le
    rw [run_paid] at hfree
    have hfp := congrArg (fun d : FreeData E n M R hR ↦ d.2.1) hfree
    have hfs := congrArg (fun d : FreeData E n M R hR ↦ d.2.2.2.1) hfree
    have hfr := congrArg (fun d : FreeData E n M R hR ↦ d.2.2.2.2) hfree
    dsimp only [freeData] at hfp hfs hfr
    change (freeState E n M R hR P seed hn q rows t (k - 2)).progress = _ at hfp
    change (freeState E n M R hR P seed hn q rows t (k - 2)).pendingStage = _ at hfs
    change (freeState E n M R hR P seed hn q rows t (k - 2)).release = _ at hfr
    rw [hprog, ← hfp]
    apply freeRequest_allowed E n M R hR hn _
      (by rw [freeState_phase E n M R hR P seed hn q rows t (k - 2) hkn]; omega)
      (by rw [freeState_phase E n M R hR P seed hn q rows t (k - 2) hkn]; omega) _ ji he
    intro hrel
    change (freeState E n M R hR P seed hn q rows t (k - 2)).pendingStage <
      (freeState E n M R hR P seed hn q rows t (k - 2)).progress.1
    rw [hfs, hfp]
    apply paidUpdate_release_frontier E n M R hR hn q _ _ rfl
    exact hfr ▸ hrel

def rawSupport (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t : ℕ) : Finset (RowIndex n M) :=
  Finset.univ.biUnion (fun τ : Fin t ↦
    (request E n M R hR hn (runWithRows E n M R hR P seed hn q rows τ.val)).elim
      (fun _ ↦ ∅) (fun ji ↦ {ji}))

theorem mem_rawSupport_iff (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t : ℕ) (ji : RowIndex n M) :
    ji ∈ rawSupport E n M R hR P seed hn q rows t ↔
      ∃ τ < t, request E n M R hR hn (runWithRows E n M R hR P seed hn q rows τ) = Sum.inr ji := by
  simp only [rawSupport, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨τ, ht⟩
    refine ⟨τ.val, τ.isLt, ?_⟩
    cases he : request E n M R hR hn (runWithRows E n M R hR P seed hn q rows τ.val) with
    | inl u => simp [he] at ht
    | inr ij =>
        simp only [he, Sum.elim_inr, Finset.mem_singleton] at ht
        simpa only [ht] using he
  · rintro ⟨τ, hτ, he⟩
    exact ⟨⟨τ, hτ⟩, by simp [he]⟩

theorem boundary_requests_allowed (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t : ℕ) :
    ∀ τ < (n + 2) * t, ∀ ji : RowIndex n M,
      request E n M R hR hn (runWithRows E n M R hR P seed hn q rows τ) = Sum.inr ji →
      RowAllowed n M (boundary E n M R hR P seed hn q rows t).progress ji := by
  induction t with
  | zero => intro τ hτ; omega
  | succ t ih =>
      intro τ hτ ji he
      rw [Nat.mul_succ] at hτ
      by_cases hold : τ < (n + 2) * t
      · rw [boundary_progress_succ]
        exact rowAllowed_step n M _ _ ji (ih τ hold ji he)
      · have hk : τ - (n + 2) * t < n + 2 := by omega
        have hidx : τ = (n + 2) * t + (τ - (n + 2) * t) := by omega
        rw [hidx] at he
        exact cycle_request_allowed E n M R hR P seed hn q rows t _ hk ji he

theorem boundary_rawSupport_upper (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t : ℕ) (ji : RowIndex n M)
    (hmem : ji ∈ rawSupport E n M R hR P seed hn q rows ((n + 2) * t))
    (hfuture : (boundary E n M R hR P seed hn q rows t).progress.1 ≤ ji.1.val) :
    ji.1.val = (boundary E n M R hR P seed hn q rows t).progress.1 ∧
      ji.2 ∈ (boundary E n M R hR P seed hn q rows t).progress.2 := by
  rcases (mem_rawSupport_iff E n M R hR P seed hn q rows _ ji).mp hmem with ⟨τ, hτ, he⟩
  rcases boundary_requests_allowed E n M R hR P seed hn q rows t τ hτ ji he with h | h
  · omega
  · exact h

end

end NCConcave16991.Haar.ConeMachine
