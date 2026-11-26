import MinimaxAudit.MeasurableExecution

/-! Append exactly one genuine scalar-jet query at a source policy's saved
output, retaining that output and increasing its cap by one. -/
open Set
namespace MinimaxAudit.EvaluatedPolicy
open VIReference.Pilot
open MeasurableExecution
noncomputable section
variable {p dx dy N : ℕ} {X : Set (Primal dx)} {Y : Set (Dual dy)}

def ScalarListRun (A : DeterministicScalarPolicy p dx dy N X Y)
    (oracle : SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy))
    (h : ScalarHistory p dx dy) (out : SaddleSpace dx dy) : Prop :=
  (∀ (i : ℕ) (hi : i < h.length), A.query (h.take i) = some h[i].1 ∧ h[i].2 = oracle h[i].1) ∧
    A.query h = none ∧ A.output h = out

/-- Replay a source transcript until its original stop. One further answer
marks the extra output-point evaluation; subsequent actions are stopped. -/
def evaluatedActionFrom (A : DeterministicScalarPolicy p dx dy N X Y)
    (initialHist : ScalarHistory p dx dy) : ScalarHistory p dx dy → OracleAction (productDomain X Y)
  | [] => match hq : A.query initialHist with
    | none => Sum.inr ⟨A.output initialHist, A.feasible_output initialHist⟩
    | some q => Sum.inr ⟨q, A.feasible_query initialHist q hq⟩
  | entry :: rest => match A.query initialHist with
    | none => Sum.inl ⟨A.output initialHist, A.feasible_output initialHist⟩
    | some _ => evaluatedActionFrom A (initialHist ++ [entry]) rest

@[simp] theorem evaluated_action_nil_query (A : DeterministicScalarPolicy p dx dy N X Y)
    (h : ScalarHistory p dx dy) :
    (match evaluatedActionFrom A h [] with
      | Sum.inl _ => none | Sum.inr q => some q.1) =
      match A.query h with | none => some (A.output h) | some q => some q := by
  unfold evaluatedActionFrom
  split
  · rename_i out heq
    split at heq <;> simp_all
  · rename_i q heq
    split at heq <;> simp_all <;> exact (congrArg Subtype.val heq).symm

theorem evaluated_action_stops_at_cap (A : DeterministicScalarPolicy p dx dy N X Y)
    (initialHist rest : ScalarHistory p dx dy)
    (hpre : initialHist.length ≤ N) (hlen : N + 1 ≤ initialHist.length + rest.length) :
    ∃ out, evaluatedActionFrom A initialHist rest = Sum.inl out := by
  induction rest generalizing initialHist with
  | nil => simp only [List.length_nil, Nat.add_zero] at hlen; omega
  | cons entry rest ih =>
    cases hq : A.query initialHist with
    | none => exact ⟨⟨A.output initialHist, A.feasible_output initialHist⟩, by simp [evaluatedActionFrom, hq]⟩
    | some q =>
      have hlt : initialHist.length < N := by
        by_contra hn
        have hstop := A.cap initialHist (by omega)
        rw [hq] at hstop
        contradiction
      obtain ⟨out, hout⟩ := ih (initialHist ++ [entry]) (by simp; omega) (by simp_all; omega)
      exact ⟨out, by simpa [evaluatedActionFrom, hq] using hout⟩

def evaluatedPolicy (A : DeterministicScalarPolicy p dx dy N X Y) :
    DeterministicScalarPolicy p dx dy (N + 1) X Y where
  query h := match evaluatedActionFrom A [] h with
    | Sum.inl _ => none | Sum.inr q => some q.1
  output h := match evaluatedActionFrom A [] h with
    | Sum.inl out => out.1 | Sum.inr _ => A.output h
  cap h hh := by
    obtain ⟨out, ho⟩ := evaluated_action_stops_at_cap A [] h (by simp) (by simpa using hh)
    rw [ho]
  feasible_query h z hz := by
    cases ha : evaluatedActionFrom A [] h with
    | inl out => simp [ha] at hz
    | inr q => simp only [ha, Option.some.injEq] at hz; simpa [← hz] using q.property
  feasible_output h := by
    cases ha : evaluatedActionFrom A [] h with
    | inl out => exact out.property
    | inr q => exact A.feasible_output h

/-- Replaying a recorded active prefix neither stops early nor loses its
saved history. This lemma has no oracle assumptions. -/
theorem evaluated_action_replay (A : DeterministicScalarPolicy p dx dy N X Y)
    (entries initialHist tail : ScalarHistory p dx dy)
    (hq : ∀ (i : ℕ) (hi : i < entries.length), A.query (initialHist ++ entries.take i) ≠ none) :
    evaluatedActionFrom A initialHist (entries ++ tail) =
      evaluatedActionFrom A (initialHist ++ entries) tail := by
  induction entries generalizing initialHist with
  | nil => simp
  | cons entry entries ih =>
    have hfirst := hq 0 (by simp)
    simp only [List.take_zero, List.append_nil] at hfirst
    cases ha : A.query initialHist with
    | none => contradiction
    | some q =>
      simp only [List.cons_append, evaluatedActionFrom, ha]
      have he := ih (initialHist ++ [entry]) (by
        intro i hi
        have h := hq (i + 1) (by simpa using Nat.succ_lt_succ hi)
        simpa [List.take_succ_cons, List.append_assoc] using h)
      simpa [List.append_assoc] using he

/-- The wrapper still issues the original recorded query at each active
proper prefix, then issues exactly the original output point. -/
theorem evaluated_query_at_prefix (A : DeterministicScalarPolicy p dx dy N X Y)
    (oracle : SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy))
    (h : ScalarHistory p dx dy) (out : SaddleSpace dx dy) (hrun : ScalarListRun A oracle h out)
    (i : ℕ) (hi : i ≤ h.length) :
    (evaluatedPolicy A).query (h.take i) =
      if hlt : i < h.length then some h[i].1 else some out := by
  have hpref : ∀ j (hj : j < (h.take i).length), A.query ((h.take i).take j) ≠ none := by
    intro j hj
    have hji : j < i := by simpa [List.length_take, Nat.min_eq_left hi] using hj
    have hjh : j < h.length := Nat.lt_of_lt_of_le hji hi
    have hq := (hrun.1 j hjh).1
    simpa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hji), hq]
  have hreplay := evaluated_action_replay A (h.take i) [] [] (by simpa using hpref)
  simp only [List.append_nil, List.nil_append] at hreplay
  change (match evaluatedActionFrom A [] (h.take i) with
    | Sum.inl _ => none | Sum.inr q => some q.1) = _
  rw [hreplay, evaluated_action_nil_query]
  by_cases hlt : i < h.length
  · simp [ (hrun.1 i hlt).1, hlt]
  · have heq : i = h.length := by omega
    subst i
    simp [hrun.2.1, hrun.2.2]

theorem evaluated_stop_after_output_query (A : DeterministicScalarPolicy p dx dy N X Y)
    (oracle : SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy))
    (h : ScalarHistory p dx dy) (out : SaddleSpace dx dy) (hrun : ScalarListRun A oracle h out) :
    (evaluatedPolicy A).query (h ++ [(out, oracle out)]) = none ∧
      (evaluatedPolicy A).output (h ++ [(out, oracle out)]) = out := by
  have hreplay := evaluated_action_replay A h [] [(out, oracle out)] (by
    intro i hi
    simp only [List.nil_append]
    rw [(hrun.1 i hi).1]
    simp)
  simp only [List.nil_append] at hreplay
  have ha : evaluatedActionFrom A [] (h ++ [(out, oracle out)]) =
      Sum.inl ⟨A.output h, A.feasible_output h⟩ := by
    rw [hreplay]
    simp [evaluatedActionFrom, hrun.2.1]
  simp [evaluatedPolicy, ha, hrun.2.2]

/-- Every capped source policy has an actual finite stopped transcript. -/
theorem exists_recorded_continuation (A : DeterministicScalarPolicy p dx dy N X Y)
    (oracle : SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy))
    (fuel : ℕ) (initialHist : ScalarHistory p dx dy) (hcap : N ≤ initialHist.length + fuel) :
    ∃ entries : ScalarHistory p dx dy, entries.length ≤ fuel ∧
      (∀ (i : ℕ) (hi : i < entries.length),
        A.query (initialHist ++ entries.take i) = some entries[i].1 ∧ entries[i].2 = oracle entries[i].1) ∧
      A.query (initialHist ++ entries) = none ∧
      A.output (initialHist ++ entries) = Deterministic.runScalarPolicy A oracle fuel initialHist := by
  induction fuel generalizing initialHist with
  | zero =>
    refine ⟨[], by simp, ?_, ?_, ?_⟩
    · simp
    · simpa using A.cap initialHist (by simpa using hcap)
    · simp [Deterministic.runScalarPolicy]
  | succ fuel ih =>
    cases hq : A.query initialHist with
    | none =>
      refine ⟨[], by simp, by simp, ?_, ?_⟩
      · simpa using hq
      · simp [Deterministic.runScalarPolicy, hq]
    | some q =>
      obtain ⟨entries, hlen, hqueries, hstop, hout⟩ :=
        ih (initialHist ++ [(q, oracle q)]) (by simp_all; omega)
      refine ⟨(q, oracle q) :: entries, by simp; omega, ?_, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero => simpa using And.intro hq (rfl : oracle q = oracle q)
        | succ i =>
          have h := hqueries i (by simpa using hi)
          simpa [List.take_succ_cons, List.append_assoc] using h
      · simpa [List.append_assoc] using hstop
      · simpa [List.append_assoc, Deterministic.runScalarPolicy, hq] using hout

theorem exists_recorded_run (A : DeterministicScalarPolicy p dx dy N X Y)
    (oracle : SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy)) :
    ∃ h : ScalarHistory p dx dy, h.length ≤ N ∧
      ScalarListRun A oracle h (Deterministic.runScalarPolicy A oracle N []) := by
  obtain ⟨h, hlen, hq, hs, ho⟩ := exists_recorded_continuation A oracle N [] (by simp)
  exact ⟨h, hlen, by simpa [ScalarListRun] using And.intro hq (And.intro hs ho)⟩

/-- One real endpoint query is appended to the genuine stopped transcript,
with the same saved output and at most N+1 total scalar-jet calls. -/
theorem evaluated_policy_recorded_run (A : DeterministicScalarPolicy p dx dy N X Y)
    (oracle : SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy))
    (h : ScalarHistory p dx dy) (out : SaddleSpace dx dy)
    (hrun : ScalarListRun A oracle h out) (hlen : h.length ≤ N) :
    ∃ hEval : ScalarHistory p dx dy, hEval.length ≤ N + 1 ∧
      ScalarListRun (evaluatedPolicy A) oracle hEval out ∧
      (out, oracle out) ∈ hEval ∧
      Deterministic.runScalarPolicy (evaluatedPolicy A) oracle (N + 1) [] = out := by
  let hEval := h ++ [(out, oracle out)]
  have hlenEval : hEval.length ≤ N + 1 := by simp [hEval]; omega
  have hqueries : ∀ (i : ℕ) (hi : i < hEval.length),
      (evaluatedPolicy A).query (hEval.take i) = some hEval[i].1 ∧
      hEval[i].2 = oracle hEval[i].1 := by
    intro i hi
    have hi' : i ≤ h.length := by dsimp [hEval] at hi; simp only [List.length_append, List.length_singleton] at hi; omega
    have htake : hEval.take i = h.take i := by
      simp [hEval, List.take_append, Nat.sub_eq_zero_of_le hi']
    have hq := evaluated_query_at_prefix A oracle h out hrun i hi'
    by_cases hlt : i < h.length
    · rw [htake, hq]
      simpa [hEval, List.getElem_append, hlt] using
        And.intro (by simp [hlt] : (if _ : i < h.length then some h[i].1 else some out) = some h[i].1)
          (hrun.1 i hlt).2
    · have hieq : i = h.length := by omega
      subst i
      rw [htake, hq]
      simp [hEval]
  have hstop := evaluated_stop_after_output_query A oracle h out hrun
  have htrace : ScalarListRun (evaluatedPolicy A) oracle hEval out :=
    ⟨hqueries, hstop.1, hstop.2⟩
  refine ⟨hEval, hlenEval, htrace, ?_, ?_⟩
  · simp [hEval]
  · exact run_eq_of_recorded_list (evaluatedPolicy A) oracle hEval [] out (N + 1) hlenEval
      (by simpa using hqueries) (by simpa using hstop.1) (by simpa using hstop.2)

/-- The evaluation wrapper preserves every actual output and provides an
explicit genuine queried-output transcript witness. -/
theorem evaluated_policy_preserves_output (A : DeterministicScalarPolicy p dx dy N X Y)
    (oracle : SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy)) :
    Deterministic.runScalarPolicy (evaluatedPolicy A) oracle (N + 1) [] =
      Deterministic.runScalarPolicy A oracle N [] ∧
    ∃ hEval : ScalarHistory p dx dy, hEval.length ≤ N + 1 ∧
      ScalarListRun (evaluatedPolicy A) oracle hEval
        (Deterministic.runScalarPolicy (evaluatedPolicy A) oracle (N + 1) []) ∧
      (Deterministic.runScalarPolicy (evaluatedPolicy A) oracle (N + 1) [],
        oracle (Deterministic.runScalarPolicy (evaluatedPolicy A) oracle (N + 1) [])) ∈ hEval := by
  obtain ⟨h, hlen, hrun⟩ := exists_recorded_run A oracle
  obtain ⟨he, hle, htrace, hmem, hout⟩ := evaluated_policy_recorded_run A oracle h _ hrun hlen
  exact ⟨hout, he, hle, by simpa only [hout] using htrace, by simpa only [hout] using hmem⟩

end
end MinimaxAudit.EvaluatedPolicy
