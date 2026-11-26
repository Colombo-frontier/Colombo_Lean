import NCConcave16991.ConditionalHaarOptionalReveal

/-!
# Actual frontier bookkeeping for the cone revelation protocol

One paid component query inserts one row at the current frontier. At the
ceiling of n/4096 distinct rows, that frontier advances and its full row block
may be revealed for free. A literal potential proves the paid query lower
bound and the small learned fraction at every unfinished frontier.
-/

open MeasureTheory

namespace NCConcave16991.Haar.ConeCounter

noncomputable section

def threshold (n : ℕ) : ℕ := (n + 4095) / 4096

abbrev State (n : ℕ) := ℕ × Finset (Fin n)

instance revealedIndexSetMeasurableSpace (n : ℕ) : MeasurableSpace (Finset (Fin n)) := ⊤

instance revealedIndexSetMeasurableSingletonClass (n : ℕ) : MeasurableSingletonClass (Finset (Fin n)) :=
  ⟨fun _ ↦ trivial⟩

def initial (n : ℕ) : State n := (0, ∅)

def step {n : ℕ} (s : State n) (query : Option (Fin n)) : State n :=
  match query with
  | none => s
  | some i =>
    let A := insert i s.2
    if threshold n ≤ A.card then (s.1 + 1, ∅) else (s.1, A)

def work {n : ℕ} (s : State n) : ℕ := s.1 * threshold n + s.2.card

def run {n : ℕ} (query : ℕ → Option (Fin n)) : ℕ → State n
  | 0 => initial n
  | t + 1 => step (run query t) (query t)

theorem threshold_pos {n : ℕ} (hn : 0 < n) : 0 < threshold n := by
  unfold threshold
  omega

theorem threshold_scaled_lower (n : ℕ) : n ≤ 4096 * threshold n := by
  unfold threshold
  omega

theorem step_measurable (n : ℕ) : Measurable (fun p : State n × Option (Fin n) ↦ step p.1 p.2) :=
  measurable_of_countable _

theorem work_step_le {n : ℕ} (s : State n) (query : Option (Fin n)) :
    work (step s query) ≤ work s + 1 := by
  cases query with
  | none => simp [step]
  | some i =>
    have hc : (insert i s.2).card ≤ s.2.card + 1 := Finset.card_insert_le _ _
    dsimp only [step]
    split_ifs with h
    · simp only [work, Finset.card_empty, add_zero, Nat.add_mul, Nat.one_mul]
      omega
    · simp only [work]
      omega

theorem step_learned_lt {n : ℕ} (hn : 0 < n) (s : State n)
    (hs : s.2.card < threshold n) (query : Option (Fin n)) :
    (step s query).2.card < threshold n := by
  cases query with
  | none => exact hs
  | some i =>
    dsimp only [step]
    split_ifs with h
    · simpa using threshold_pos hn
    · exact Nat.lt_of_not_ge h

theorem work_run_le {n : ℕ} (query : ℕ → Option (Fin n)) (t : ℕ) : work (run query t) ≤ t := by
  induction t with
  | zero => simp [run, initial, work]
  | succ t ih => exact (work_step_le (run query t) (query t)).trans (Nat.add_le_add_right ih 1)

theorem run_learned_lt {n : ℕ} (hn : 0 < n) (query : ℕ → Option (Fin n)) (t : ℕ) :
    (run query t).2.card < threshold n := by
  induction t with
  | zero => simpa [run, initial] using threshold_pos hn
  | succ t ih => exact step_learned_lt hn (run query t) ih (query t)

theorem learned_fraction_le {n : ℕ} (A : Finset (Fin n)) (hA : A.card < threshold n) :
    (A.card : ℝ) ≤ (n : ℝ) / 4096 := by
  have hc : 4096 * A.card < n := by unfold threshold at hA; omega
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4096)).mpr
  have hreal : (4096 : ℝ) * (A.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hc.le
  nlinarith

/-- Completing every stage costs at least n/4096 paid queries per stage,
including early stopping and repeated component choices. -/
theorem completed_stages_cost {n : ℕ} (query : ℕ → Option (Fin n)) (t stages : ℕ)
    (hdone : stages ≤ (run query t).1) :
    (stages : ℝ) * (n : ℝ) / 4096 ≤ (t : ℝ) := by
  have hc : stages * threshold n ≤ t := by
    have hmul := Nat.mul_le_mul_right (threshold n) hdone
    have hwork := work_run_le query t
    unfold work at hwork
    omega
  have hs : (n : ℝ) ≤ 4096 * (threshold n : ℝ) := by exact_mod_cast threshold_scaled_lower n
  have hc' : (stages : ℝ) * (threshold n : ℝ) ≤ (t : ℝ) := by exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg stages : (0 : ℝ) ≤ stages)
  nlinarith

theorem unfinished_of_budget_lt {n : ℕ} (query : ℕ → Option (Fin n)) (t stages : ℕ)
    (hbudget : (t : ℝ) < (n : ℝ) * (stages : ℝ) / 4096) :
    (run query t).1 < stages := by
  by_contra h
  have hc := completed_stages_cost query t stages (Nat.le_of_not_gt h)
  nlinarith

end

end NCConcave16991.Haar.ConeCounter
