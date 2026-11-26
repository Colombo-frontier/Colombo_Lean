import Mathlib.Data.List.Basic

/-!
# Deterministic finite-transcript replay

This file proves the generic replay step used in `geode.tex`, Section 6.
Queries depend on the entire ordered history, and the output is unrestricted.
The simulation may answer adaptively; a fixed oracle agreeing on its queried
points reproduces that simulation exactly.

This is a reusable oracle-model result. It does not construct the hyperbolic
objective, prove legal subgradients, or assert the manuscript's lower bound.
The first API has a specified finite query horizon. The second API models
history-dependent stopping and a finite query budget. Exhaustion records the
next requested query. Divergent internal computation is not modeled.
-/

namespace Geode
namespace OracleReplay

universe u v w

abbrev History (Point : Type u) (Reply : Type v) := List (Point × Reply)

/-- A deterministic rule may use all previous query locations and replies.
The output need not be one of the previously queried points. -/
structure Algorithm (Point : Type u) (Reply : Type v) where
  query : History Point Reply → Point
  output : History Point Reply → Point

variable {Point : Type u} {Reply : Type v}

/-- An adaptive simulation may inspect the history as well as the new query. -/
abbrev Responder (Point : Type u) (Reply : Type v) :=
  History Point Reply → Point → Reply

/-- The actual ordered query/reply history, defined by recursion. -/
def transcript (A : Algorithm Point Reply) (respond : Responder Point Reply) :
    ℕ → History Point Reply
  | 0 => []
  | n + 1 =>
    let h := transcript A respond n
    let x := A.query h
    h ++ [(x, respond h x)]

def fixedResponder (oracle : Point → Reply) : Responder Point Reply :=
  fun _ x => oracle x

def queryAt (A : Algorithm Point Reply) (respond : Responder Point Reply) (n : ℕ) :
    Point := A.query (transcript A respond n)

def replyAt (A : Algorithm Point Reply) (respond : Responder Point Reply) (n : ℕ) :
    Reply := respond (transcript A respond n) (queryAt A respond n)

def result (A : Algorithm Point Reply) (respond : Responder Point Reply) (n : ℕ) :
    Point := A.output (transcript A respond n)

theorem transcript_length (A : Algorithm Point Reply) (respond : Responder Point Reply)
    (n : ℕ) : (transcript A respond n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [transcript, ih]

/-- Agreement is needed only at the queries the simulation actually makes. -/
def AgreesThrough (A : Algorithm Point Reply) (respond : Responder Point Reply)
    (oracle : Point → Reply) (N : ℕ) : Prop :=
  ∀ i < N, oracle (queryAt A respond i) = replyAt A respond i

theorem agreesThrough_mono (A : Algorithm Point Reply) (respond : Responder Point Reply)
    (oracle : Point → Reply) {n N : ℕ} (h : AgreesThrough A respond oracle N)
    (hn : n ≤ N) : AgreesThrough A respond oracle n := by
  intro i hi
  exact h i (Nat.lt_of_lt_of_le hi hn)

/-- The induction proves equality of complete histories, including queries. -/
theorem fixed_oracle_replays (A : Algorithm Point Reply) (respond : Responder Point Reply)
    (oracle : Point → Reply) (N : ℕ) (h : AgreesThrough A respond oracle N) :
    transcript A (fixedResponder oracle) N = transcript A respond N := by
  induction N with
  | zero => rfl
  | succ n ih =>
    have hprev := agreesThrough_mono A respond oracle h (Nat.le_succ n)
    have ht := ih hprev
    have hlast := h n (Nat.lt_succ_self n)
    simp only [queryAt, replyAt] at hlast
    simp only [transcript, fixedResponder, ht, hlast]

theorem fixed_oracle_replays_prefix (A : Algorithm Point Reply)
    (respond : Responder Point Reply) (oracle : Point → Reply) {n N : ℕ}
    (h : AgreesThrough A respond oracle N) (hn : n ≤ N) :
    transcript A (fixedResponder oracle) n = transcript A respond n :=
  fixed_oracle_replays A respond oracle n (agreesThrough_mono A respond oracle h hn)

theorem fixed_oracle_replays_query (A : Algorithm Point Reply)
    (respond : Responder Point Reply) (oracle : Point → Reply) {n N : ℕ}
    (h : AgreesThrough A respond oracle N) (hn : n ≤ N) :
    queryAt A (fixedResponder oracle) n = queryAt A respond n := by
  unfold queryAt
  rw [fixed_oracle_replays_prefix A respond oracle h hn]

theorem fixed_oracle_replays_output (A : Algorithm Point Reply)
    (respond : Responder Point Reply) (oracle : Point → Reply) (N : ℕ)
    (h : AgreesThrough A respond oracle N) :
    result A (fixedResponder oracle) N = result A respond N := by
  unfold result
  rw [fixed_oracle_replays A respond oracle N h]

/-- Every observation in the recursive transcript is one of its indexed replies. -/
theorem mem_transcript_iff (A : Algorithm Point Reply) (respond : Responder Point Reply)
    (N : ℕ) (x : Point) (r : Reply) :
    (x, r) ∈ transcript A respond N ↔
      ∃ i < N, queryAt A respond i = x ∧ replyAt A respond i = r := by
  induction N with
  | zero => simp [transcript]
  | succ n ih =>
    simp only [transcript, List.mem_append, List.mem_singleton, ih]
    constructor
    · intro h
      rcases h with h | h
      · obtain ⟨i, hi, hx, hr⟩ := h
        exact ⟨i, Nat.lt_succ_of_lt hi, hx, hr⟩
      · have hx : queryAt A respond n = x := (Prod.mk.inj h).1.symm
        have hr : replyAt A respond n = r := (Prod.mk.inj h).2.symm
        exact ⟨n, Nat.lt_succ_self n, hx, hr⟩
    · rintro ⟨i, hi, hx, hr⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact Or.inl ⟨i, hi, hx, hr⟩
      · subst i
        exact Or.inr (Prod.ext hx.symm hr.symm)

/-- A single-valued completion must give the same reply at repeated queries. -/
theorem repeated_queries_same_reply (A : Algorithm Point Reply)
    (respond : Responder Point Reply) (oracle : Point → Reply) {N i j : ℕ}
    (h : AgreesThrough A respond oracle N) (hi : i < N) (hj : j < N)
    (hquery : queryAt A respond i = queryAt A respond j) :
    replyAt A respond i = replyAt A respond j := by
  rw [← h i hi, ← h j hj, hquery]

/-- A finite history can be realized by a function only if repeated locations
have identical replies. The manuscript enforces this using its reply cache. -/
def Consistent (history : History Point Reply) : Prop :=
  ∀ x r s, (x, r) ∈ history → (x, s) ∈ history → r = s

/-- Patch the fallback selection at the finitely many observed locations. -/
noncomputable def cachedOracle (history : History Point Reply)
    (fallback : Point → Reply) (x : Point) : Reply := by
  classical
  exact if h : ∃ r, (x, r) ∈ history then Classical.choose h else fallback x

theorem cachedOracle_realizes (history : History Point Reply)
    (fallback : Point → Reply) (hconsistent : Consistent history)
    {x : Point} {r : Reply} (hmem : (x, r) ∈ history) :
    cachedOracle history fallback x = r := by
  classical
  have hex : ∃ r, (x, r) ∈ history := ⟨r, hmem⟩
  simp only [cachedOracle, dif_pos hex]
  exact hconsistent x _ r (Classical.choose_spec hex) hmem

theorem cachedOracle_unqueried (history : History Point Reply)
    (fallback : Point → Reply) {x : Point} (hunqueried : ∀ r, (x, r) ∉ history) :
    cachedOracle history fallback x = fallback x := by
  classical
  have hnot : ¬ ∃ r, (x, r) ∈ history := by
    rintro ⟨r, hr⟩
    exact hunqueried r hr
  simp only [cachedOracle, dif_neg hnot]

/-- If every archived reply and the fallback are legal, patching is legal
everywhere. This applies to full value/subgradient pairs as the `Reply` type. -/
theorem cachedOracle_legal (history : History Point Reply) (fallback : Point → Reply)
    (LegalReply : Point → Reply → Prop)
    (harchive : ∀ x r, (x, r) ∈ history → LegalReply x r)
    (hfallback : ∀ x, LegalReply x (fallback x)) :
    ∀ x, LegalReply x (cachedOracle history fallback x) := by
  classical
  intro x
  by_cases h : ∃ r, (x, r) ∈ history
  · simp only [cachedOracle, dif_pos h]
    exact harchive x _ (Classical.choose_spec h)
  · simp only [cachedOracle, dif_neg h]
    exact hfallback x

/-- Construct a single fixed legal oracle realizing the entire simulation.
The geometric completion must separately supply `harchive` and `hfallback`. -/
theorem complete_consistent_transcript (A : Algorithm Point Reply)
    (respond : Responder Point Reply) (N : ℕ) (fallback : Point → Reply)
    (LegalReply : Point → Reply → Prop)
    (hconsistent : Consistent (transcript A respond N))
    (harchive : ∀ x r, (x, r) ∈ transcript A respond N → LegalReply x r)
    (hfallback : ∀ x, LegalReply x (fallback x)) :
    ∃ oracle : Point → Reply, (∀ x, LegalReply x (oracle x)) ∧
      AgreesThrough A respond oracle N := by
  refine ⟨cachedOracle (transcript A respond N) fallback,
    cachedOracle_legal _ _ LegalReply harchive hfallback, ?_⟩
  intro i hi
  apply cachedOracle_realizes _ _ hconsistent
  exact (mem_transcript_iff A respond N _ _).2 ⟨i, hi, rfl, rfl⟩

/-- Failure on the simulated unrestricted output transfers to the fixed oracle.
`Legal` and `Fails` are arbitrary predicates; producing a legal completion and
proving its failure are separate geometric obligations. -/
theorem failure_transfers {Instance : Type w}
    (A : Algorithm Point Reply) (respond : Responder Point Reply) (N : ℕ)
    (Legal : Instance → (Point → Reply) → Prop) (Fails : Instance → Point → Prop)
    (completion : ∃ inst oracle, Legal inst oracle ∧
      AgreesThrough A respond oracle N ∧ Fails inst (result A respond N)) :
    ∃ inst oracle, Legal inst oracle ∧
      Fails inst (result A (fixedResponder oracle) N) := by
  obtain ⟨inst, oracle, hlegal, hagree, hfail⟩ := completion
  refine ⟨inst, oracle, hlegal, ?_⟩
  rw [fixed_oracle_replays_output A respond oracle N hagree]
  exact hfail

/-! ## Algorithms with history-dependent stopping -/

/-- Stopping returns any point; it does not have to be an observed query. -/
inductive Decision (Point : Type u) where
  | stop : Point → Decision Point
  | query : Point → Decision Point

structure StoppingAlgorithm (Point : Type u) (Reply : Type v) where
  decide : History Point Reply → Decision Point

/-- `exhausted h x` means the algorithm has requested the next query `x`
after spending the available query budget. It is not a claim of nontermination. -/
inductive RunResult (Point : Type u) (Reply : Type v) where
  | finished : History Point Reply → Point → RunResult Point Reply
  | exhausted : History Point Reply → Point → RunResult Point Reply

def RunResult.history : RunResult Point Reply → History Point Reply
  | .finished h _ => h
  | .exhausted h _ => h

/-- A stop decision is allowed even with zero query budget remaining. A query
decision consumes one unit only when an oracle response is actually obtained. -/
def run (A : StoppingAlgorithm Point Reply) (respond : Responder Point Reply) :
    ℕ → History Point Reply → RunResult Point Reply
  | 0, h => match A.decide h with
    | .stop x => .finished h x
    | .query x => .exhausted h x
  | n + 1, h => match A.decide h with
    | .stop x => .finished h x
    | .query x => run A respond n (h ++ [(x, respond h x)])

/-- All earlier observations persist, whether the run stops or exhausts fuel. -/
theorem mem_run_history (A : StoppingAlgorithm Point Reply)
    (respond : Responder Point Reply) (n : ℕ) (h : History Point Reply)
    {entry : Point × Reply} (hmem : entry ∈ h) :
    entry ∈ (run A respond n h).history := by
  induction n generalizing h with
  | zero => cases hdecision : A.decide h <;> simpa [run, hdecision, RunResult.history]
  | succ n ih =>
    cases hdecision : A.decide h with
    | stop x => simpa [run, hdecision, RunResult.history]
    | query x =>
      simp only [run, hdecision]
      apply ih
      exact List.mem_append_left _ hmem

/-- Agreement with the final archive suffices: no conditions are imposed on
points the simulation never queries. Initial history is normally `[]`. -/
theorem stopping_fixed_oracle_replays (A : StoppingAlgorithm Point Reply)
    (respond : Responder Point Reply) (oracle : Point → Reply)
    (n : ℕ) (h : History Point Reply)
    (hagree : ∀ x r, (x, r) ∈ (run A respond n h).history → oracle x = r) :
    run A (fixedResponder oracle) n h = run A respond n h := by
  induction n generalizing h with
  | zero => cases hdecision : A.decide h <;> simp [run, hdecision]
  | succ n ih =>
    cases hdecision : A.decide h with
    | stop x => simp [run, hdecision]
    | query x =>
      have hnew : (x, respond h x) ∈
          (run A respond n (h ++ [(x, respond h x)])).history := by
        apply mem_run_history
        exact List.mem_append_right _ (by simp)
      have hreply : oracle x = respond h x := by
        apply hagree x (respond h x)
        simpa only [run, hdecision] using hnew
      simp only [run, hdecision, fixedResponder, hreply]
      apply ih
      simpa only [run, hdecision] using hagree

/-- The same early stopping time, complete archive, and output are reproduced. -/
theorem stopping_replays_finished (A : StoppingAlgorithm Point Reply)
    (respond : Responder Point Reply) (oracle : Point → Reply)
    (n : ℕ) (h finalHistory : History Point Reply) (output : Point)
    (hfinished : run A respond n h = .finished finalHistory output)
    (hagree : ∀ x r, (x, r) ∈ finalHistory → oracle x = r) :
    run A (fixedResponder oracle) n h = .finished finalHistory output := by
  have hreplay := stopping_fixed_oracle_replays A respond oracle n h
    (by simpa only [hfinished, RunResult.history] using hagree)
  exact hreplay.trans hfinished

/-- A request beyond the budget is also reproduced, including its location. -/
theorem stopping_replays_exhausted (A : StoppingAlgorithm Point Reply)
    (respond : Responder Point Reply) (oracle : Point → Reply)
    (n : ℕ) (h finalHistory : History Point Reply) (nextQuery : Point)
    (hexhausted : run A respond n h = .exhausted finalHistory nextQuery)
    (hagree : ∀ x r, (x, r) ∈ finalHistory → oracle x = r) :
    run A (fixedResponder oracle) n h = .exhausted finalHistory nextQuery := by
  have hreplay := stopping_fixed_oracle_replays A respond oracle n h
    (by simpa only [hexhausted, RunResult.history] using hagree)
  exact hreplay.trans hexhausted

/-- Every execution makes at most its allowed number of additional queries. -/
theorem run_history_length_le (A : StoppingAlgorithm Point Reply)
    (respond : Responder Point Reply) (n : ℕ) (h : History Point Reply) :
    (run A respond n h).history.length ≤ h.length + n := by
  induction n generalizing h with
  | zero => cases hdecision : A.decide h <;> simp [run, hdecision, RunResult.history]
  | succ n ih =>
    cases hdecision : A.decide h with
    | stop x => simp [run, hdecision, RunResult.history]
    | query x =>
      simp only [run, hdecision]
      simpa [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        using ih (h ++ [(x, respond h x)])

/-- Exhaustion entails spending exactly the available query budget. -/
theorem exhausted_history_length (A : StoppingAlgorithm Point Reply)
    (respond : Responder Point Reply) (n : ℕ) (h finalHistory : History Point Reply)
    (nextQuery : Point) (hexhausted : run A respond n h = .exhausted finalHistory nextQuery) :
    finalHistory.length = h.length + n := by
  induction n generalizing h with
  | zero =>
    cases hdecision : A.decide h with
    | stop x => simp [run, hdecision] at hexhausted
    | query x =>
      have hh : h = finalHistory := (RunResult.exhausted.inj
        (by simpa [run, hdecision] using hexhausted)).1
      simp [← hh]
  | succ n ih =>
    cases hdecision : A.decide h with
    | stop x => simp [run, hdecision] at hexhausted
    | query x =>
      have he : run A respond n (h ++ [(x, respond h x)]) =
          .exhausted finalHistory nextQuery := by simpa [run, hdecision] using hexhausted
      simpa [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        using ih (h ++ [(x, respond h x)]) he

/-- A consistent legal archive has a fixed legal completion reproducing the
same stopped or exhausted execution, using the explicit cached oracle. -/
theorem complete_stopping_run (A : StoppingAlgorithm Point Reply)
    (respond : Responder Point Reply) (N : ℕ) (fallback : Point → Reply)
    (LegalReply : Point → Reply → Prop)
    (hconsistent : Consistent (run A respond N []).history)
    (harchive : ∀ x r, (x, r) ∈ (run A respond N []).history → LegalReply x r)
    (hfallback : ∀ x, LegalReply x (fallback x)) :
    ∃ oracle : Point → Reply, (∀ x, LegalReply x (oracle x)) ∧
      run A (fixedResponder oracle) N [] = run A respond N [] := by
  let oracle := cachedOracle (run A respond N []).history fallback
  refine ⟨oracle, cachedOracle_legal _ _ LegalReply harchive hfallback, ?_⟩
  apply stopping_fixed_oracle_replays
  intro x r hr
  exact cachedOracle_realizes _ _ hconsistent hr

/-- Either a bad output or a request beyond the query budget defeats the
budget-and-output guarantee. This definition deliberately does not include
divergence of the algorithm's internal computation. -/
def RunFails (Fails : Point → Prop) : RunResult Point Reply → Prop
  | .finished _ output => Fails output
  | .exhausted _ _ => True

theorem stopping_failure_transfers {Instance : Type w}
    (A : StoppingAlgorithm Point Reply) (respond : Responder Point Reply) (N : ℕ)
    (Legal : Instance → (Point → Reply) → Prop) (Fails : Instance → Point → Prop)
    (completion : ∃ inst oracle, Legal inst oracle ∧
      (∀ x r, (x, r) ∈ (run A respond N []).history → oracle x = r) ∧
      RunFails (Fails inst) (run A respond N [])) :
    ∃ inst oracle, Legal inst oracle ∧
      RunFails (Fails inst) (run A (fixedResponder oracle) N []) := by
  obtain ⟨inst, oracle, hlegal, hagree, hfail⟩ := completion
  refine ⟨inst, oracle, hlegal, ?_⟩
  rw [stopping_fixed_oracle_replays A respond oracle N [] hagree]
  exact hfail

end OracleReplay
end Geode
