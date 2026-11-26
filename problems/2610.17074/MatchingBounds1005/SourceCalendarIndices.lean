import MatchingBounds1005.SourceReferenceProgram

/-! Exact physical-query and terminal-candidate positions in the compiled
calendar. Arbitrarily many disclosures at one time leave the public clock
unchanged. -/
set_option autoImplicit false
noncomputable section

namespace MatchingBounds1005.ReadoutCalendar
open ScheduledHaar
variable {N : ℕ}

def queryIndex (τ : Fin N → ℕ) : ℕ → ℕ → ℕ
  | start, 0 => (VisibleReadouts.due τ start).length
  | start, j + 1 => (VisibleReadouts.due τ start).length + 1 + queryIndex τ (start + 1) j

def candidateIndex (τ : Fin N → ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | start, H + 1 => (VisibleReadouts.due τ start).length + 1 + candidateIndex τ (start + 1) H

theorem commandClock_prepend (xs : List (Fin N)) (w : List SourceKind) (start j : ℕ) :
    commandClock (prependKinds xs w) start (xs.length + j) = commandClock w start j := by
  induction xs with
  | nil => simp [prependKinds]
  | cons i xs ih => simpa [prependKinds, commandClock, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using ih

theorem getElem?_prepend (xs : List (Fin N)) (w : List SourceKind) (j : ℕ) :
    (prependKinds xs w)[xs.length + j]? = w[j]? := by
  unfold prependKinds
  rw [List.getElem?_append_right (by simp)]
  simp

theorem candidateIndex_length (τ : Fin N → ℕ) (start H : ℕ) :
    candidateIndex τ start H + 1 = (kinds τ start H).length := by
  induction H generalizing start with
  | zero => rfl
  | succ H ih =>
      simp only [candidateIndex, kinds, prependKinds, List.length_append, List.length_map,
        List.length_cons, ← ih]
      omega

theorem queryIndex_lt_candidateIndex (τ : Fin N → ℕ) (start H j : ℕ) (hj : j < H) :
    queryIndex τ start j < candidateIndex τ start H := by
  induction H generalizing start j with
  | zero => omega
  | succ H ih =>
      cases j with
      | zero => simp only [queryIndex, candidateIndex]; omega
      | succ j =>
          have h := ih (start + 1) j (by omega)
          simp only [queryIndex, candidateIndex]
          omega

theorem queryIndex_lt_length (τ : Fin N → ℕ) (start H j : ℕ) (hj : j < H) :
    queryIndex τ start j < (kinds τ start H).length := by
  have h := queryIndex_lt_candidateIndex τ start H j hj
  have he := candidateIndex_length τ start H
  omega

theorem candidateIndex_lt_length (τ : Fin N → ℕ) (start H : ℕ) :
    candidateIndex τ start H < (kinds τ start H).length := by
  have h := candidateIndex_length τ start H
  omega

theorem commandClock_queryIndex (τ : Fin N → ℕ) (start H j : ℕ) (hj : j < H) :
    commandClock (kinds τ start H) start (queryIndex τ start j) = start + j := by
  induction H generalizing start j with
  | zero => omega
  | succ H ih =>
      cases j with
      | zero =>
          rw [kinds, queryIndex]
          simpa only [Nat.add_zero, commandClock_zero] using
            commandClock_prepend (VisibleReadouts.due τ start)
              (.query :: kinds τ (start + 1) H) start 0
      | succ j =>
          rw [kinds, queryIndex, Nat.add_assoc, commandClock_prepend]
          rw [Nat.one_add]
          change commandClock (kinds τ (start + 1) H) (start + 1)
            (queryIndex τ (start + 1) j) = _
          rw [ih (start + 1) j (by omega)]
          omega

theorem commandClock_candidateIndex (τ : Fin N → ℕ) (start H : ℕ) :
    commandClock (kinds τ start H) start (candidateIndex τ start H) = start + H := by
  induction H generalizing start with
  | zero => simp [kinds, candidateIndex]
  | succ H ih =>
      rw [kinds, candidateIndex, Nat.add_assoc, commandClock_prepend]
      rw [Nat.one_add]
      change commandClock (kinds τ (start + 1) H) (start + 1)
        (candidateIndex τ (start + 1) H) = _
      rw [ih]
      omega

theorem getElem?_queryIndex (τ : Fin N → ℕ) (start H j : ℕ) (hj : j < H) :
    (kinds τ start H)[queryIndex τ start j]? = some .query := by
  induction H generalizing start j with
  | zero => omega
  | succ H ih =>
      cases j with
      | zero =>
          rw [kinds, queryIndex]
          simpa using getElem?_prepend (VisibleReadouts.due τ start)
            (.query :: kinds τ (start + 1) H) 0
      | succ j =>
          rw [kinds, queryIndex, Nat.add_assoc, getElem?_prepend]
          simpa only [Nat.one_add, List.getElem?_cons_succ] using ih (start + 1) j (by omega)

theorem getElem?_candidateIndex (τ : Fin N → ℕ) (start H : ℕ) :
    (kinds τ start H)[candidateIndex τ start H]? = some .candidate := by
  induction H generalizing start with
  | zero => rfl
  | succ H ih =>
      rw [kinds, candidateIndex, Nat.add_assoc, getElem?_prepend]
      simpa only [Nat.one_add, List.getElem?_cons_succ] using ih (start + 1)

theorem queryIndex_lt_succ (τ : Fin N → ℕ) (start j : ℕ) :
    queryIndex τ start j < queryIndex τ start (j + 1) := by
  induction j generalizing start with
  | zero => simp only [queryIndex]; omega
  | succ j ih =>
      have h := ih (start + 1)
      change (VisibleReadouts.due τ start).length + 1 + queryIndex τ (start + 1) j <
        (VisibleReadouts.due τ start).length + 1 + queryIndex τ (start + 1) (j + 1)
      exact Nat.add_lt_add_left h _

theorem queryIndex_strictMono (τ : Fin N → ℕ) (start : ℕ) :
    StrictMono (queryIndex τ start) := strictMono_nat_of_lt_succ (queryIndex_lt_succ τ start)

end MatchingBounds1005.ReadoutCalendar

namespace MatchingBounds1005.SourceReferenceProgram
open ScheduledHaar
variable {d N : ℕ}

def queryIndex (P : Parameters d N) (j : ℕ) : ℕ := 1 + ReadoutCalendar.queryIndex P.disclosure 1 j
def candidateIndex (P : Parameters d N) (H : ℕ) : ℕ :=
  1 + ReadoutCalendar.candidateIndex P.disclosure 1 H

theorem queryIndex_lt_length (P : Parameters d N) (H j : ℕ) (hj : j < H) :
    queryIndex P j < (commands P H).length := by
  have h := ReadoutCalendar.queryIndex_lt_length P.disclosure 1 H j hj
  simp only [queryIndex, commands, List.length_cons]
  omega

theorem candidateIndex_lt_length (P : Parameters d N) (H : ℕ) :
    candidateIndex P H < (commands P H).length := by
  have h := ReadoutCalendar.candidateIndex_lt_length P.disclosure 1 H
  simp only [candidateIndex, commands, List.length_cons]
  omega

theorem candidateIndex_length (P : Parameters d N) (H : ℕ) :
    candidateIndex P H + 1 = (commands P H).length := by
  have h := ReadoutCalendar.candidateIndex_length P.disclosure 1 H
  simp only [candidateIndex, commands, List.length_cons]
  omega

theorem queryIndex_lt_candidateIndex (P : Parameters d N) (H j : ℕ) (hj : j < H) :
    queryIndex P j < candidateIndex P H := Nat.add_lt_add_left
      (ReadoutCalendar.queryIndex_lt_candidateIndex P.disclosure 1 H j hj) 1

theorem queryIndex_strictMono (P : Parameters d N) : StrictMono (queryIndex P) := by
  intro i j hij
  exact Nat.add_lt_add_left (ReadoutCalendar.queryIndex_strictMono P.disclosure 1 hij) 1

theorem commandClock_queryIndex (P : Parameters d N) (H j : ℕ) (hj : j < H) :
    commandClock (commands P H) 1 (queryIndex P j) = j + 1 := by
  simp only [commands, queryIndex, Nat.one_add, commandClock]
  simpa only [Nat.add_comm] using ReadoutCalendar.commandClock_queryIndex P.disclosure 1 H j hj

theorem commandClock_candidateIndex (P : Parameters d N) (H : ℕ) :
    commandClock (commands P H) 1 (candidateIndex P H) = H + 1 := by
  simp only [commands, candidateIndex, Nat.one_add, commandClock]
  simpa only [Nat.add_comm] using ReadoutCalendar.commandClock_candidateIndex P.disclosure 1 H

theorem getElem?_queryIndex (P : Parameters d N) (H j : ℕ) (hj : j < H) :
    (commands P H)[queryIndex P j]? = some .query := by
  simpa only [commands, queryIndex, Nat.one_add, List.getElem?_cons_succ] using
    ReadoutCalendar.getElem?_queryIndex P.disclosure 1 H j hj

theorem getElem?_candidateIndex (P : Parameters d N) (H : ℕ) :
    (commands P H)[candidateIndex P H]? = some .candidate := by
  simpa only [commands, candidateIndex, Nat.one_add, List.getElem?_cons_succ] using
    ReadoutCalendar.getElem?_candidateIndex P.disclosure 1 H

/-- The compact observation list contains the physical queries followed by
the frozen output, and is embedded in the full analyst command list. -/
def observationIndex (P : Parameters d N) (H : ℕ) (i : Fin (H + 1)) :
    Fin (commands P H).length :=
  if hi : i.val < H then ⟨queryIndex P i.val, queryIndex_lt_length P H i.val hi⟩
  else ⟨candidateIndex P H, candidateIndex_lt_length P H⟩

theorem observationIndex_query (P : Parameters d N) (H : ℕ) (i : Fin H) :
    (observationIndex P H i.castSucc).val = queryIndex P i.val := by
  simp [observationIndex, i.isLt]

theorem observationIndex_candidate (P : Parameters d N) (H : ℕ) :
    (observationIndex P H (Fin.last H)).val = candidateIndex P H := by
  simp [observationIndex]

theorem observationIndex_clock (P : Parameters d N) (H : ℕ) (i : Fin (H + 1)) :
    commandClock (commands P H) 1 (observationIndex P H i).val = i.val + 1 := by
  unfold observationIndex
  split_ifs with hi
  · exact commandClock_queryIndex P H i.val hi
  · have he : i.val = H := by omega
    simpa only [he] using commandClock_candidateIndex P H

theorem observationIndex_strictMono (P : Parameters d N) (H : ℕ) :
    StrictMono (observationIndex P H) := by
  intro i j hij
  have hv : i.val < j.val := hij
  have hi : i.val < H := by omega
  unfold observationIndex
  rw [dif_pos hi]
  split_ifs with hj
  · exact queryIndex_strictMono P hv
  · exact queryIndex_lt_candidateIndex P H i.val hi

end MatchingBounds1005.SourceReferenceProgram
