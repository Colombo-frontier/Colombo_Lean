import NCConcave16991.DenseSmoothCensoredCost
import NCConcave16991.DenseSmoothRevelationCensor

/-! # Actual precompletion queries occur in the fresh-row compiler trace -/

namespace NCConcave16991.DenseSmooth.Revelation

noncomputable section

open DenseWeakHiding

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable (n T D : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)
  {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n)
    (dx := primalDimension (CensoredSpace D) T) Ω)

theorem freshAnswer_at_stage (seed : Ω) (A : Table (CensoredSpace D) n T ρ)
    (s : State (CensoredSpace D) n T hn ρ hρ) (j : Fin (T + 1))
    (hj : frontier (CensoredSpace D) n T hn ρ hρ s = j.val) :
    (freshRequest (CensoredSpace D) n T hn ρ hρ P seed s).elim 0 (fun ji ↦ A.row ji.2 ji.1) =
      (censoredRequest (CensoredSpace D) n T hn ρ hρ P seed s).elim 0 (fun i ↦ A.row i j) := by
  cases hr : request (CensoredSpace D) n T hn ρ hρ P seed s with
  | none => simp [freshRequest,censoredRequest,hr]
  | some ji =>
      have he : ji.1 = j := Fin.ext ((request_stage (CensoredSpace D) n T hn ρ hρ P seed s ji hr).trans hj)
      by_cases hi : ji.2 ∈ s.base.progress.2 <;>
        simp [freshRequest,censoredRequest,hr,hi,Option.filter,he]

theorem bits_actualStep_eq_precompletion (seed : Ω) (A : Table (CensoredSpace D) n T ρ)
    (s : State (CensoredSpace D) n T hn ρ hρ)
    (hs : CurrentCorrect (CensoredSpace D) n T hn ρ hρ A s)
    (j : Fin (T + 1)) (hj : frontier (CensoredSpace D) n T hn ρ hρ s = j.val)
    (table : Fin n → FreshCompiler.Reply D) (hrow : ∀ i, normalizedReply (table i) = A.row i j) :
    FreshCompiler.actualStep (bitsRequest n T D hn ρ hρ P seed)
      (bitsAdvance n T D hn ρ hρ P seed) table s =
      precompletionStep (CensoredSpace D) n T hn ρ hρ P seed s
        ((request (CensoredSpace D) n T hn ρ hρ P seed s).elim 0 (fun ji ↦ A.row ji.2 ji.1)) := by
  rw [precompletionStep_eq_fresh (CensoredSpace D) n T hn ρ hρ P seed A s hs,
    freshAnswer_at_stage n T D hn ρ hρ P seed A s j hj]
  unfold FreshCompiler.actualStep bitsAdvance
  cases hr : bitsRequest n T D hn ρ hρ P seed s with
  | none =>
      have hc : censoredRequest (CensoredSpace D) n T hn ρ hρ P seed s = none := hr
      simp only [hr,hc,Option.elim_none]
      exact censoredAdvance_none_eq n T D hn ρ hρ P seed s hr _ _
  | some i =>
      have hc : censoredRequest (CensoredSpace D) n T hn ρ hρ P seed s = some i := hr
      simp only [hr,hc,Option.elim_some,hrow]

section Generic

variable {S : Type*} {N K : ℕ} (req : S → Option (Fin N))
  (adv : S → FreshCompiler.Reply K → S) (table : Fin N → FreshCompiler.Reply K)

theorem compiler_actualRun_succ (t : ℕ) (s : S) :
    FreshCompiler.actualRun req adv table (t + 1) s =
      FreshCompiler.actualStep req adv table (FreshCompiler.actualRun req adv table t s) := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih => exact ih (FreshCompiler.actualStep req adv table s)

end Generic

theorem bits_actualRun_eq_censored (seed : Ω) (A : Table (CensoredSpace D) n T ρ)
    (s : State (CensoredSpace D) n T hn ρ hρ)
    (hs : CurrentCorrect (CensoredSpace D) n T hn ρ hρ A s)
    (j : Fin (T + 1)) (hj : frontier (CensoredSpace D) n T hn ρ hρ s = j.val)
    (table : Fin n → FreshCompiler.Reply D) (hrow : ∀ i, normalizedReply (table i) = A.row i j)
    (t : ℕ) :
    FreshCompiler.actualRun (bitsRequest n T D hn ρ hρ P seed)
      (bitsAdvance n T D hn ρ hρ P seed) table t s =
      censoredRunFrom (CensoredSpace D) n T hn ρ hρ P seed (fun i ↦ A.row i j) s t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [compiler_actualRun_succ,ih]
      have hc := censoredRunFrom_currentCorrect (CensoredSpace D) n T hn ρ hρ P seed A s hs j hj t
      have hf : frontier (CensoredSpace D) n T hn ρ hρ
          (censoredRunFrom (CensoredSpace D) n T hn ρ hρ P seed (fun i ↦ A.row i j) s t) = j.val := by
        rw [censoredRunFrom_frontier,hj]
      rw [bits_actualStep_eq_precompletion n T D hn ρ hρ P seed A _ hc j hf table hrow,
        rowAnswer_at_stage (CensoredSpace D) n T hn ρ hρ P seed A _ j hf]
      rfl

theorem censored_mem_cutTrace (seed : Ω) (A : Table (CensoredSpace D) n T ρ)
    (s : State (CensoredSpace D) n T hn ρ hρ)
    (hs : CurrentCorrect (CensoredSpace D) n T hn ρ hρ A s)
    (j : Fin (T + 1)) (hj : frontier (CensoredSpace D) n T hn ρ hρ s = j.val)
    (table : Fin n → FreshCompiler.Reply D) (hrow : ∀ i, normalizedReply (table i) = A.row i j)
    (fuel r t : ℕ) (ht : t ≤ fuel)
    (hc : (censoredRunFrom (CensoredSpace D) n T hn ρ hρ P seed (fun i ↦ A.row i j) s t).assigned j < r) :
    censoredRunFrom (CensoredSpace D) n T hn ρ hρ P seed (fun i ↦ A.row i j) s t ∈
      FreshCompiler.cutTrace (bitsRequest n T D hn ρ hρ P seed)
        (bitsAdvance n T D hn ρ hρ P seed) table r fuel s := by
  have he := bits_actualRun_eq_censored n T D hn ρ hρ P seed A s hs j hj table hrow t
  have hb := bits_reads_le_cost n T hn ρ hρ D P seed table t s j hj
  rw [he] at hb
  have hr : FreshCompiler.readsBefore (bitsRequest n T D hn ρ hρ P seed)
      (bitsAdvance n T D hn ρ hρ P seed) table t s < r := by omega
  exact he ▸ FreshCompiler.actualRun_mem_cutTrace _ _ table fuel r t s ht hr

theorem initialized_actualRun_inr (seed : Ω) (i₀ : Fin n)
    (start : CensoredSpace D → State (CensoredSpace D) n T hn ρ hρ)
    (table : Fin n → FreshCompiler.Reply D) (t : ℕ)
    (s : State (CensoredSpace D) n T hn ρ hρ) :
    FreshCompiler.actualRun (initializedBitsRequest n T D hn ρ hρ P seed i₀)
      (initializedBitsAdvance n T D hn ρ hρ P seed start) table t (.inr s) =
      .inr (FreshCompiler.actualRun (bitsRequest n T D hn ρ hρ P seed)
        (bitsAdvance n T D hn ρ hρ P seed) table t s) := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih => exact ih _

theorem initialized_actualRun_eq_censored (seed : Ω) (i₀ : Fin n)
    (start : CensoredSpace D → State (CensoredSpace D) n T hn ρ hρ)
    (A : Table (CensoredSpace D) n T ρ) (j : Fin (T + 1))
    (table : Fin n → FreshCompiler.Reply D) (hrow : ∀ i, normalizedReply (table i) = A.row i j)
    (hs : CurrentCorrect (CensoredSpace D) n T hn ρ hρ A (start (normalizedReply (table i₀))))
    (hj : frontier (CensoredSpace D) n T hn ρ hρ (start (normalizedReply (table i₀))) = j.val)
    (t : ℕ) :
    FreshCompiler.actualRun (initializedBitsRequest n T D hn ρ hρ P seed i₀)
      (initializedBitsAdvance n T D hn ρ hρ P seed start) table (t + 1) (.inl ()) =
      .inr (censoredRunFrom (CensoredSpace D) n T hn ρ hρ P seed (fun i ↦ A.row i j)
        (start (normalizedReply (table i₀))) t) := by
  change FreshCompiler.actualRun (initializedBitsRequest n T D hn ρ hρ P seed i₀)
    (initializedBitsAdvance n T D hn ρ hρ P seed start) table t
      (Sum.inr (start (normalizedReply (table i₀)))) = _
  rw [initialized_actualRun_inr,bits_actualRun_eq_censored n T D hn ρ hρ P seed A _ hs j hj table hrow]

theorem initialized_censored_mem_cutTrace (seed : Ω) (i₀ : Fin n)
    (start : CensoredSpace D → State (CensoredSpace D) n T hn ρ hρ)
    (A : Table (CensoredSpace D) n T ρ) (j : Fin (T + 1))
    (table : Fin n → FreshCompiler.Reply D) (hrow : ∀ i, normalizedReply (table i) = A.row i j)
    (hs : CurrentCorrect (CensoredSpace D) n T hn ρ hρ A (start (normalizedReply (table i₀))))
    (hstart : ∀ a, frontier (CensoredSpace D) n T hn ρ hρ (start a) = j.val)
    (fuel r t : ℕ) (ht : t + 1 ≤ fuel)
    (hc : (censoredRunFrom (CensoredSpace D) n T hn ρ hρ P seed (fun i ↦ A.row i j)
        (start (normalizedReply (table i₀))) t).assigned j + 1 < r) :
    .inr (censoredRunFrom (CensoredSpace D) n T hn ρ hρ P seed (fun i ↦ A.row i j)
        (start (normalizedReply (table i₀))) t) ∈
      FreshCompiler.cutTrace (initializedBitsRequest n T D hn ρ hρ P seed i₀)
        (initializedBitsAdvance n T D hn ρ hρ P seed start) table r fuel (.inl ()) := by
  have he := initialized_actualRun_eq_censored n T D hn ρ hρ P seed i₀ start A j table hrow hs (hstart _) t
  have hb := initialized_reads_le_cost n T hn ρ hρ D P seed i₀ start j hstart table (t + 1)
  rw [he] at hb
  change FreshCompiler.readsBefore (initializedBitsRequest n T D hn ρ hρ P seed i₀)
    (initializedBitsAdvance n T D hn ρ hρ P seed start) table (t + 1) (Sum.inl ()) ≤ _ + 1 at hb
  have hr : FreshCompiler.readsBefore (initializedBitsRequest n T D hn ρ hρ P seed i₀)
      (initializedBitsAdvance n T D hn ρ hρ P seed start) table (t + 1) (.inl ()) < r := by omega
  exact he ▸ FreshCompiler.actualRun_mem_cutTrace
    (initializedBitsRequest n T D hn ρ hρ P seed i₀)
    (initializedBitsAdvance n T D hn ρ hρ P seed start) table fuel r (t + 1) (Sum.inl ()) ht hr

end
end NCConcave16991.DenseSmooth.Revelation
