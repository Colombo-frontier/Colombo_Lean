import NCConcave16991.BranchOracleResponse
import NCConcave16991.BranchOracleGrowth

/-! # The actual finite-history branch reference interpreter -/

namespace NCConcave16991.BranchOracle.Reference
noncomputable section
open GlobalHard GlobalHardEuclidean

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 1000000

variable {n M N : ℕ} [NeZero n] (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, FiniteDimensional ℝ (V j k)]
variable {D : ℝ} (K : KnownDualDomain (dualDimension V) D)

structure State where
  profile : WordProfile (Fin n)
  released : ℕ
  history : OraclePolicy.History K (n := n) (dx := primalDimension V)

def initial : State (n := n) V K := ⟨WordProfile.root, 0, OraclePolicy.emptyHistory K⟩

variable (B : ∀ j : Fin M, ∀ t : Fin N,
    BranchGeometry.BranchFamily (ι := Fin n) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))
  (ρ : ℝ) (site : Fin M → ℕ) (d c μ : ℝ)

/-- One component query uses one simultaneous selected-index matrix round,
then closes the public source rule, and appends the rendered complete reply. -/
def step (s : State (n := n) V K) (q : OracleQuery n (primalDimension V) K) : State (n := n) V K :=
  let a := WordProfile.close ρ site s.released (s.profile.matrixScheduleStep (fun _ ↦ q.1))
  ⟨a.2, a.1, OraclePolicy.appendHistory K s.history
    (q, referenceResponse V K B u v a.1 d c μ q)⟩

theorem step_history_length (s : State (n := n) V K) (q : OracleQuery n (primalDimension V) K) :
    (step V K B u v ρ site d c μ s q).history.1 = s.history.1 + 1 := rfl

theorem step_scheduledRun (s : State (n := n) V K) (q : OracleQuery n (primalDimension V) K)
    (h : WordProfile.ScheduledRun ρ s.history.1 s.released s.profile) :
    WordProfile.ScheduledRun ρ (step V K B u v ρ site d c μ s q).history.1
      (step V K B u v ρ site d c μ s q).released (step V K B u v ρ site d c μ s q).profile :=
  WordProfile.close_scheduledRun ρ site s.released (s.history.1 + 1) _ (WordProfile.ScheduledRun.matrix h (fun _ ↦ q.1))

theorem step_released_le (s : State (n := n) V K) (q : OracleQuery n (primalDimension V) K) (hr : s.released ≤ M) :
    (step V K B u v ρ site d c μ s q).released ≤ M :=
  (WordProfile.close_release_bound ρ site s.released _ hr).2

theorem step_closed (hsite : Monotone site) (s : State (n := n) V K) (q : OracleQuery n (primalDimension V) K) :
    WordProfile.ReleaseClosed ρ site (step V K B u v ρ site d c μ s q).released
      (step V K B u v ρ site d c μ s q).profile := WordProfile.close_closed ρ site hsite _ _

theorem step_words_extend (s : State (n := n) V K) (q : OracleQuery n (primalDimension V) K) :
    WordProfile.WordsExtend s.profile (step V K B u v ρ site d c μ s q).profile :=
  WordProfile.roundClosure_words_extend ρ site s.released s.profile (fun _ ↦ q.1)

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy K (n := n) (dx := primalDimension V) Ω)

def runAux (seed : Ω) : ℕ → State (n := n) V K → PrimalSpace (primalDimension V) × State (n := n) V K
  | 0, s => (P.final seed s.history, s)
  | t + 1, s => match P.next seed s.history with
    | Sum.inl x => (x, s)
    | Sum.inr q => runAux seed t (step V K B u v ρ site d c μ s q)

def run (seed : Ω) (budget : ℕ) := runAux V K B u v ρ site d c μ P seed budget (initial V K)

theorem runAux_budget (seed : Ω) (t : ℕ) (s : State (n := n) V K) :
    (runAux V K B u v ρ site d c μ P seed t s).2.history.1 ≤ s.history.1 + t := by
  induction t generalizing s with
  | zero => simp [runAux]
  | succ t ih =>
    cases hn : P.next seed s.history with
    | inl x => simp [runAux, hn]
    | inr q =>
      have hh := ih (step V K B u v ρ site d c μ s q)
      simpa only [runAux, hn, step_history_length, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem runAux_scheduledRun (seed : Ω) (t : ℕ) (s : State (n := n) V K)
    (h : WordProfile.ScheduledRun ρ s.history.1 s.released s.profile) :
    WordProfile.ScheduledRun ρ (runAux V K B u v ρ site d c μ P seed t s).2.history.1
      (runAux V K B u v ρ site d c μ P seed t s).2.released
      (runAux V K B u v ρ site d c μ P seed t s).2.profile := by
  induction t generalizing s with
  | zero => exact h
  | succ t ih =>
    cases hn : P.next seed s.history with
    | inl x => simpa only [runAux, hn] using h
    | inr q => simpa only [runAux, hn] using ih _ (step_scheduledRun V K B u v ρ site d c μ s q h)

theorem run_scheduledRun (seed : Ω) (budget : ℕ) :
    WordProfile.ScheduledRun ρ (run V K B u v ρ site d c μ P seed budget).2.history.1
      (run V K B u v ρ site d c μ P seed budget).2.released
      (run V K B u v ρ site d c μ P seed budget).2.profile :=
  runAux_scheduledRun V K B u v ρ site d c μ P seed budget (initial V K) WordProfile.ScheduledRun.initial

def StepFlat (s : State (n := n) V K) (q : OracleQuery n (primalDimension V) K) : Prop :=
  ∀ j : Fin M, (step V K B u v ρ site d c μ s q).released ≤ j.val →
    stateScore (v j) (stateProj V j (queryGlobal V K q)) < deltaGate

def RunFlat (seed : Ω) : ℕ → State (n := n) V K → Prop
  | 0, _ => True
  | t + 1, s => match P.next seed s.history with
    | Sum.inl _ => True
    | Sum.inr q => StepFlat V K B u v ρ site d c μ s q ∧
        RunFlat seed t (step V K B u v ρ site d c μ s q)

/-- On the common flat event, the actual complete histories and arbitrary
outputs agree with the genuine component-oracle run, including early stops. -/
theorem runAux_eq_true (seed : Ω) (t : ℕ) (s : State (n := n) V K)
    (hflat : RunFlat V K B u v ρ site d c μ P seed t s) :
    ((runAux V K B u v ρ site d c μ P seed t s).1,
      (runAux V K B u v ρ site d c μ P seed t s).2.history) =
      OraclePolicy.runAux K P (trueComponentAnswer V K B u v d c μ) seed t s.history := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
    cases hn : P.next seed s.history with
    | inl x => simp only [runAux, OraclePolicy.runAux, hn]
    | inr q =>
      simp only [RunFlat, hn] at hflat
      have ha := referenceResponse_eq_true_of_flat V K B u v
        (step V K B u v ρ site d c μ s q).released d c μ q hflat.1
      have hh : (step V K B u v ρ site d c μ s q).history =
          OraclePolicy.appendHistory K s.history (q, trueComponentAnswer V K B u v d c μ q) := by
        change OraclePolicy.appendHistory K s.history (q, referenceResponse V K B u v
          (step V K B u v ρ site d c μ s q).released d c μ q) = _
        rw [ha]
      simpa only [runAux, OraclePolicy.runAux, hn, hh] using ih _ hflat.2

end
end NCConcave16991.BranchOracle.Reference
