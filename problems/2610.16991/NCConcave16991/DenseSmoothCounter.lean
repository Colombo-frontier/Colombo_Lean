import NCConcave16991.ConditionalHaarConeCounter

/-! # Literal paid-row accounting for a configurable dense-stage threshold -/

namespace NCConcave16991.DenseSmooth.Counter

abbrev State (n : ℕ) := ℕ × Finset (Fin n)

def initial (n : ℕ) : State n := (0, ∅)

def step {n : ℕ} (r : ℕ) (s : State n) (query : Option (Fin n)) : State n :=
  match query with
  | none => s
  | some i => if r ≤ (insert i s.2).card then (s.1 + 1, ∅) else (s.1, insert i s.2)

def work {n : ℕ} (r : ℕ) (s : State n) : ℕ := s.1 * r + s.2.card

def run {n : ℕ} (r : ℕ) (query : ℕ → Option (Fin n)) : ℕ → State n
  | 0 => initial n
  | t + 1 => step r (run r query t) (query t)

theorem work_step_le {n : ℕ} (r : ℕ) (s : State n) (query : Option (Fin n)) :
    work r (step r s query) ≤ work r s + 1 := by
  cases query with
  | none => simp [step]
  | some i =>
      have hc : (insert i s.2).card ≤ s.2.card + 1 := Finset.card_insert_le _ _
      dsimp only [step]
      split_ifs <;> simp only [work, Finset.card_empty, add_zero, Nat.add_mul, Nat.one_mul] <;> omega

theorem step_learned_lt {n : ℕ} {r : ℕ} (hr : 0 < r) (s : State n)
    (hs : s.2.card < r) (query : Option (Fin n)) : (step r s query).2.card < r := by
  cases query with
  | none => exact hs
  | some i => dsimp only [step]; split_ifs <;> simp_all

theorem work_run_le {n : ℕ} (r : ℕ) (query : ℕ → Option (Fin n)) (t : ℕ) : work r (run r query t) ≤ t := by
  induction t with
  | zero => simp [run, initial, work]
  | succ t ih => exact (work_step_le r (run r query t) (query t)).trans (Nat.add_le_add_right ih 1)

theorem run_learned_lt {n : ℕ} {r : ℕ} (hr : 0 < r) (query : ℕ → Option (Fin n)) (t : ℕ) :
    (run r query t).2.card < r := by
  induction t with
  | zero => simpa [run, initial] using hr
  | succ t ih => exact step_learned_lt hr _ ih _

theorem unfinished_of_budget {n : ℕ} (r : ℕ) (query : ℕ → Option (Fin n)) (t stages : ℕ)
    (hbudget : t < stages * r) : (run r query t).1 < stages := by
  have hh := work_run_le r query t
  unfold work at hh
  by_contra h
  have hm := Nat.mul_le_mul_right r (Nat.le_of_not_gt h)
  omega

end NCConcave16991.DenseSmooth.Counter
