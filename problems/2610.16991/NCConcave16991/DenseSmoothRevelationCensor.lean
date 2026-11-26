import NCConcave16991.DenseSmoothRevelationFresh

/-! # Exact histories and queries through the first alignment completion -/

namespace NCConcave16991.DenseSmooth.Revelation

noncomputable section

open Set MeasureTheory

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n T : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)
  {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n) (dx := primalDimension E T) Ω)

def runFromTable (seed : Ω) (A : Table E n T ρ) (s : State E n T hn ρ hρ) : ℕ → State E n T hn ρ hρ
  | 0 => s
  | t + 1 => stepWithTable E n T hn ρ hρ P seed A (runFromTable seed A s t)

theorem request_stage (seed : Ω) (s : State E n T hn ρ hρ) (ji : Machine.RowIndex n T)
    (hr : request E n T hn ρ hρ P seed s = some ji) : ji.1.val = frontier E n T hn ρ hρ s :=
  Machine.request_stage E n T hn ρ hρ P seed s.base ji hr

theorem rowAnswer_at_stage (seed : Ω) (A : Table E n T ρ) (s : State E n T hn ρ hρ)
    (j : Fin (T + 1)) (hj : frontier E n T hn ρ hρ s = j.val) :
    (request E n T hn ρ hρ P seed s).elim 0 (fun ji ↦ A.row ji.2 ji.1) =
      (request E n T hn ρ hρ P seed s).elim 0 (fun ji ↦ A.row ji.2 j) := by
  cases hr : request E n T hn ρ hρ P seed s with
  | none => rfl
  | some ji =>
      have he : ji.1 = j := Fin.ext ((request_stage E n T hn ρ hρ P seed s ji hr).trans hj)
      simp only [Option.elim_some, he]

theorem runFrom_eq_censored (seed : Ω) (A : Table E n T ρ) (s : State E n T hn ρ hρ)
    (j : Fin (T + 1)) (hj : frontier E n T hn ρ hρ s = j.val) (q : ℕ)
    (hno : ∀ t < q, completion E n T hn ρ hρ P seed A (runFromTable E n T hn ρ hρ P seed A s t) = false) :
    runFromTable E n T hn ρ hρ P seed A s q =
      censoredRunFrom E n T hn ρ hρ P seed (fun i ↦ A.row i j) s q := by
  have hall : ∀ q, (∀ t < q, completion E n T hn ρ hρ P seed A (runFromTable E n T hn ρ hρ P seed A s t) = false) →
      runFromTable E n T hn ρ hρ P seed A s q = censoredRunFrom E n T hn ρ hρ P seed (fun i ↦ A.row i j) s q := by
    intro q
    induction q with
    | zero => intro _; rfl
    | succ q ih =>
        intro hno
        have he := ih (fun t ht ↦ hno t (by omega))
        have hf : frontier E n T hn ρ hρ (runFromTable E n T hn ρ hρ P seed A s q) = j.val := by
          rw [he, censoredRunFrom_frontier, hj]
        rw [runFromTable, stepWithTable_noncompletion E n T hn ρ hρ P seed A _ (hno q (by omega)),
          rowAnswer_at_stage E n T hn ρ hρ P seed A _ j hf, he]
        rfl
  exact hall q hno

theorem firstCompletion_query_eq_censored (seed : Ω) (A : Table E n T ρ) (s : State E n T hn ρ hρ)
    (j : Fin (T + 1)) (hj : frontier E n T hn ρ hρ s = j.val) (q : ℕ)
    (hno : ∀ t < q, completion E n T hn ρ hρ P seed A (runFromTable E n T hn ρ hρ P seed A s t) = false) :
    action E n T hn ρ hρ P seed (runFromTable E n T hn ρ hρ P seed A s q) =
      action E n T hn ρ hρ P seed (censoredRunFrom E n T hn ρ hρ P seed (fun i ↦ A.row i j) s q) := by
  rw [runFrom_eq_censored E n T hn ρ hρ P seed A s j hj q hno]

theorem censoredRunFrom_currentCorrect (seed : Ω) (A : Table E n T ρ) (s : State E n T hn ρ hρ)
    (hs : CurrentCorrect E n T hn ρ hρ A s) (j : Fin (T + 1))
    (hj : frontier E n T hn ρ hρ s = j.val) (q : ℕ) :
    CurrentCorrect E n T hn ρ hρ A (censoredRunFrom E n T hn ρ hρ P seed (fun i ↦ A.row i j) s q) := by
  induction q with
  | zero => exact hs
  | succ q ih =>
      rw [censoredRunFrom]
      have hf : frontier E n T hn ρ hρ (censoredRunFrom E n T hn ρ hρ P seed (fun i ↦ A.row i j) s q) = j.val := by
        rw [censoredRunFrom_frontier, hj]
      rw [← rowAnswer_at_stage E n T hn ρ hρ P seed A _ j hf]
      exact precompletionStep_currentCorrect E n T hn ρ hρ P seed A _ ih

end

end NCConcave16991.DenseSmooth.Revelation
