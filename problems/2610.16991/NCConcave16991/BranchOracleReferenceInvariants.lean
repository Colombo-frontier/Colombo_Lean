import NCConcave16991.BranchOracleInterpreter

/-! # Actual reference runs have bounded releases and legal terminal accounting -/

namespace NCConcave16991.BranchOracle.Reference
noncomputable section
open GlobalHard GlobalHardEuclidean

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

variable {n M N : ℕ} [NeZero n] (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, FiniteDimensional ℝ (V j k)]
variable {D : ℝ} (K : KnownDualDomain (dualDimension V) D)
variable (B : ∀ j : Fin M, ∀ t : Fin N,
    BranchGeometry.BranchFamily (ι := Fin n) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))
  (ρ : ℝ) (site : Fin M → ℕ) (d c μ : ℝ)
variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy K (n := n) (dx := primalDimension V) Ω)

theorem runAux_released_le (seed : Ω) (t : ℕ) (s : State (n := n) V K) (hr : s.released ≤ M) :
    (runAux V K B u v ρ site d c μ P seed t s).2.released ≤ M := by
  induction t generalizing s with
  | zero => exact hr
  | succ t ih =>
    cases hn : P.next seed s.history with
    | inl x => simpa only [runAux, hn] using hr
    | inr q => simpa only [runAux, hn] using ih _ (step_released_le V K B u v ρ site d c μ s q hr)

theorem run_released_le (seed : Ω) (budget : ℕ) :
    (run V K B u v ρ site d c μ P seed budget).2.released ≤ M :=
  runAux_released_le V K B u v ρ site d c μ P seed budget (initial V K) (Nat.zero_le M)

theorem run_budget (seed : Ω) (budget : ℕ) :
    (run V K B u v ρ site d c μ P seed budget).2.history.1 ≤ budget := by
  simpa only [run, initial, OraclePolicy.emptyHistory, Nat.zero_add] using
    runAux_budget V K B u v ρ site d c μ P seed budget (initial V K)

theorem runAux_words_extend (seed : Ω) (t : ℕ) (s : State (n := n) V K) :
    WordProfile.WordsExtend s.profile (runAux V K B u v ρ site d c μ P seed t s).2.profile := by
  induction t generalizing s with
  | zero => exact WordProfile.WordsExtend.refl _
  | succ t ih =>
    cases hn : P.next seed s.history with
    | inl x => simpa only [runAux, hn] using WordProfile.WordsExtend.refl s.profile
    | inr q => simpa only [runAux, hn] using
        (step_words_extend V K B u v ρ site d c μ s q).trans (ih _)

theorem runAux_closed (hsite : Monotone site) (seed : Ω) (t : ℕ) (s : State (n := n) V K)
    (hs : WordProfile.ReleaseClosed ρ site s.released s.profile) :
    WordProfile.ReleaseClosed ρ site (runAux V K B u v ρ site d c μ P seed t s).2.released
      (runAux V K B u v ρ site d c μ P seed t s).2.profile := by
  induction t generalizing s with
  | zero => exact hs
  | succ t ih =>
    cases hn : P.next seed s.history with
    | inl x => simpa only [runAux, hn] using hs
    | inr q => simpa only [runAux, hn] using ih _ (step_closed V K B u v ρ site d c μ hsite s q)

theorem initial_closed (hρ : 0 < ρ) (hsite : ∀ j, 0 < site j) :
    WordProfile.ReleaseClosed ρ site (initial (n := n) V K).released (initial (n := n) V K).profile := by
  intro j _
  have hj : site j ≠ 0 := (hsite j).ne'
  simpa only [initial, WordProfile.mass, WordProfile.root, if_neg hj, Finset.card_empty,
    Nat.cast_zero, zero_div] using hρ

theorem run_closed (hρ : 0 < ρ) (hsite : Monotone site) (hpos : ∀ j, 0 < site j)
    (seed : Ω) (budget : ℕ) :
    WordProfile.ReleaseClosed ρ site (run V K B u v ρ site d c μ P seed budget).2.released
      (run V K B u v ρ site d c μ P seed budget).2.profile :=
  runAux_closed V K B u v ρ site d c μ P hsite seed budget (initial V K) (initial_closed V K ρ site hρ hpos)

end
end NCConcave16991.BranchOracle.Reference
