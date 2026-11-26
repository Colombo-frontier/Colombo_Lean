import RationalMaterializedState254

namespace Paper254

def countedKeyedLookup {n : ℕ} {α : Type*} (fallback : α) (entries : List (Fin n×α)) (j : Fin n) : α×ℕ :=
  match entries with
  | [] => (fallback,0)
  | (i,x)::xs => if i=j then (x,1) else
      let tail := countedKeyedLookup fallback xs j
      (tail.1,tail.2+1)

theorem countedKeyedLookup_value {n : ℕ} {α : Type*} (fallback : α) (entries : List (Fin n×α)) (j : Fin n) :
    (countedKeyedLookup fallback entries j).1=keyedLookup fallback entries j := by
  induction entries with
  | nil => rfl
  | cons e xs ih =>
    rcases e with ⟨i,x⟩
    by_cases h : i=j <;> simp [countedKeyedLookup,keyedLookup,h,ih]

theorem countedKeyedLookup_cost {n : ℕ} {α : Type*} (fallback : α) (entries : List (Fin n×α)) (j : Fin n) :
    (countedKeyedLookup fallback entries j).2≤entries.length := by
  induction entries with
  | nil => simp [countedKeyedLookup]
  | cons e xs ih =>
    rcases e with ⟨i,x⟩
    by_cases h : i=j <;> simp [countedKeyedLookup,h,List.length_cons] <;> omega

theorem keyedLookup_rational {n : ℕ} (entries : List (Fin n×ℚ)) (j : Fin n) :
    keyedLookup 0 entries j=rationalLookup entries j := by
  induction entries with
  | nil => rfl
  | cons e xs ih =>
    rcases e with ⟨i,x⟩
    by_cases h : i=j <;> simp [keyedLookup,rationalLookup,h,ih]

/-- The next-state materialization performs one bounded lookup per live
destination, simultaneously discarding expired histories and adding births. -/
def countedHistoryPrune {d n : ℕ} (initial : RationalHistoryData d)
    (updated : List (Fin n×RationalHistoryData d)) (next : Finset (Fin n)) :
    List (Fin n×RationalHistoryData d)×ℕ :=
  mapWithCosts (fun e => let found := countedKeyedLookup initial updated e
    ((e,found.1),found.2)) (next.sort (·≤·))

theorem countedHistoryPrune_value {d n : ℕ} (initial : RationalHistoryData d)
    (updated : List (Fin n×RationalHistoryData d)) (next : Finset (Fin n)) :
    (countedHistoryPrune initial updated next).1=
      (next.sort (·≤·)).map (fun e => (e,keyedLookup initial updated e)) := by
  simp [countedHistoryPrune,mapWithCosts_values,countedKeyedLookup_value]

theorem countedHistoryPrune_cost {d n : ℕ} (initial : RationalHistoryData d)
    (updated : List (Fin n×RationalHistoryData d)) (next : Finset (Fin n)) :
    (countedHistoryPrune initial updated next).2≤next.card*updated.length := by
  have hh := mapWithCosts_bound (fun e =>
    let found := countedKeyedLookup initial updated e
    ((e,found.1),found.2)) (next.sort (·≤·)) updated.length
      (fun e he => countedKeyedLookup_cost initial updated e)
  simpa [countedHistoryPrune,Nat.mul_comm] using hh

end Paper254
#print axioms Paper254.countedKeyedLookup_cost
#print axioms Paper254.countedHistoryPrune_cost
