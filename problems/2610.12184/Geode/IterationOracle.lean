import Geode.OracleReplay
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# A concrete fixed-horizon iteration algorithm

The algorithm reads only its ordered observed history. It queries the initial
point, then steps from the most recent point/reply, and returns a point with
minimum observed score. Neither the oracle nor an optimum value is available
to the algorithm definition.
-/

namespace Geode.IterationOracle

open OracleReplay

universe u v
variable {Point : Type u} {Reply : Type v}

theorem exists_best_entry (score : Reply → ℝ) (h : History Point Reply) (hne : h ≠ []) :
    ∃ e ∈ h, ∀ e' ∈ h, score e.2 ≤ score e'.2 := by
  classical
  obtain ⟨e₀, he₀⟩ := List.exists_mem_of_ne_nil h hne
  obtain ⟨e, he, hmin⟩ := h.toFinset.exists_min_image (fun e => score e.2)
    ⟨e₀, List.mem_toFinset.mpr he₀⟩
  exact ⟨e, List.mem_toFinset.mp he, fun e' he' => hmin e' (List.mem_toFinset.mpr he')⟩

noncomputable def bestEntry (score : Reply → ℝ) (h : History Point Reply) (hne : h ≠ []) :
    Point × Reply := Classical.choose (exists_best_entry score h hne)

theorem bestEntry_mem (score : Reply → ℝ) (h : History Point Reply) (hne : h ≠ []) :
    bestEntry score h hne ∈ h := (Classical.choose_spec (exists_best_entry score h hne)).1

theorem bestEntry_le (score : Reply → ℝ) (h : History Point Reply) (hne : h ≠ [])
    (e : Point × Reply) (he : e ∈ h) :
    score (bestEntry score h hne).2 ≤ score e.2 :=
  (Classical.choose_spec (exists_best_entry score h hne)).2 e he

noncomputable def bestPoint (o : Point) (score : Reply → ℝ) (h : History Point Reply) :
    Point := by
  classical
  exact if hn : h ≠ [] then (bestEntry score h hn).1 else o

def nextQuery (o : Point) (step : Point → Reply → Point) (h : History Point Reply) : Point :=
  match h.getLast? with
  | none => o
  | some e => step e.1 e.2

noncomputable def algorithm (o : Point) (step : Point → Reply → Point)
    (score : Reply → ℝ) (N : ℕ) : StoppingAlgorithm Point Reply where
  decide h := if N ≤ h.length then .stop (bestPoint o score h) else .query (nextQuery o step h)

def iterate (o : Point) (step : Point → Reply → Point) (O : Point → Reply) : ℕ → Point
  | 0 => o
  | n + 1 => step (iterate o step O n) (O (iterate o step O n))

def history (o : Point) (step : Point → Reply → Point) (O : Point → Reply)
    (n : ℕ) : History Point Reply :=
  (List.range n).map (fun i => (iterate o step O i, O (iterate o step O i)))

@[simp]
theorem history_zero (o : Point) (step : Point → Reply → Point) (O : Point → Reply) :
    history o step O 0 = [] := rfl

@[simp]
theorem history_length (o : Point) (step : Point → Reply → Point) (O : Point → Reply) (n : ℕ) :
    (history o step O n).length = n := by simp [history]

theorem history_succ (o : Point) (step : Point → Reply → Point) (O : Point → Reply) (n : ℕ) :
    history o step O (n + 1) = history o step O n ++
      [(iterate o step O n, O (iterate o step O n))] := by
  simp [history, List.range_succ, List.map_append]

theorem nextQuery_history (o : Point) (step : Point → Reply → Point)
    (O : Point → Reply) (n : ℕ) : nextQuery o step (history o step O n) = iterate o step O n := by
  cases n with
  | zero => rfl
  | succ n => rw [history_succ]; simp [nextQuery, List.getLast?_concat, iterate]

theorem history_member_iff (o : Point) (step : Point → Reply → Point)
    (O : Point → Reply) (n : ℕ) (e : Point × Reply) :
    e ∈ history o step O n ↔ ∃ i < n, e = (iterate o step O i, O (iterate o step O i)) := by
  simp only [history, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, he⟩
    exact ⟨i, hi, he.symm⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨i, hi, he.symm⟩

/-- Exact execution from any canonical prefix, proved by induction on remaining
oracle calls. The same algorithm works for every fixed oracle. -/
theorem run_from_prefix (o : Point) (step : Point → Reply → Point) (score : Reply → ℝ)
    (O : Point → Reply) (N m k : ℕ) (hbudget : k + m = N) :
    run (algorithm o step score N) (fixedResponder O) m (history o step O k) =
      .finished (history o step O N) (bestPoint o score (history o step O N)) := by
  induction m generalizing k with
  | zero =>
    have hk : k = N := by omega
    subst k
    simp [run, algorithm]
  | succ m ih =>
    have hk : k < N := by omega
    simp only [run, algorithm, history_length, if_neg (Nat.not_le.mpr hk),
      nextQuery_history, fixedResponder]
    rw [← history_succ]
    exact ih (k + 1) (by omega)

theorem run_eq_finished (o : Point) (step : Point → Reply → Point) (score : Reply → ℝ)
    (O : Point → Reply) (N : ℕ) :
    run (algorithm o step score N) (fixedResponder O) N [] =
      .finished (history o step O N) (bestPoint o score (history o step O N)) := by
  simpa only [history_zero] using run_from_prefix o step score O N N 0 (Nat.zero_add N)

theorem bestPoint_history (o : Point) (step : Point → Reply → Point) (score : Reply → ℝ)
    (O : Point → Reply) (N : ℕ) (hN : 0 < N) :
    ∃ j < N, bestPoint o score (history o step O N) = iterate o step O j ∧
      ∀ i < N, score (O (iterate o step O j)) ≤ score (O (iterate o step O i)) := by
  classical
  have hne : history o step O N ≠ [] := by
    intro h
    have hn := congrArg List.length h
    simp only [history_length, List.length_nil] at hn
    omega
  let e := bestEntry score (history o step O N) hne
  obtain ⟨j, hj, he⟩ := (history_member_iff o step O N e).mp (bestEntry_mem _ _ hne)
  refine ⟨j, hj, ?_, ?_⟩
  · simp only [bestPoint, dif_pos hne]
    exact congrArg Prod.fst he
  · intro i hi
    have hm := bestEntry_le score (history o step O N) hne
      (iterate o step O i, O (iterate o step O i))
      ((history_member_iff o step O N _).mpr ⟨i, hi, rfl⟩)
    change score e.2 ≤ score (O (iterate o step O i)) at hm
    simpa only [he] using hm

/-- A positive query budget returns an actual queried iterate with least
observed score, after exactly `N` queries. -/
theorem algorithm_spec (o : Point) (step : Point → Reply → Point) (score : Reply → ℝ)
    (N : ℕ) (hN : 0 < N) (O : Point → Reply) :
    ∃ j < N,
      run (algorithm o step score N) (fixedResponder O) N [] =
        .finished (history o step O N) (iterate o step O j) ∧
      ∀ i < N, score (O (iterate o step O j)) ≤ score (O (iterate o step O i)) := by
  obtain ⟨j, hj, houtput, hbest⟩ := bestPoint_history o step score O N hN
  refine ⟨j, hj, ?_, hbest⟩
  rw [run_eq_finished, houtput]

end Geode.IterationOracle
