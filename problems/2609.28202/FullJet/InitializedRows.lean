import FullJet.RandomizedRows

open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace FullJet

def initializedAsk {α β : Type*} (initialIndex : α) (ask : β → List β → α) : List β → α
  | [] => initialIndex
  | b :: bs => ask b bs

theorem initializedAsk_run_tail {α β Ω : Type*} (initialIndex : α)
    (ask : β → List β → α) (observe : Ω → α → β) (ω : Ω) (b : β)
    (past : List β) (q : ℕ) :
    runReplies (fun ω hist => observe ω (initializedAsk initialIndex ask hist)) ω (b :: past) q =
      runReplies (fun ω hist => observe ω (ask b hist)) ω past q := by
  induction q generalizing past with
  | zero => rfl
  | succ q ih =>
    simp only [runReplies, initializedAsk.eq_2, List.cons_append, ih]

/-- A free initialization followed by `q` charged queries is exactly an
ordinary `q+1`-query run whose first index was selected before its answer. -/
theorem initializedAsk_run {α β Ω : Type*} (initialIndex : α)
    (ask : β → List β → α) (observe : Ω → α → β) (ω : Ω) (q : ℕ) :
    runReplies (fun ω hist => observe ω (initializedAsk initialIndex ask hist)) ω [] (q + 1) =
      Fin.cons (observe ω initialIndex)
        (runReplies (fun ω' hist => observe ω' (ask (observe ω initialIndex) hist)) ω [] q) := by
  rw [runReplies]
  simp only [initializedAsk.eq_1, List.nil_append, initializedAsk_run_tail]

def initializedTableRun {n D k : ℕ} (initialIndex : Fin n)
    (ask : (Fin D → Bool) → List (Fin D → Bool) → Fin n) (q : ℕ)
    (ω : FixedTableSample n D k) : (Fin D → Bool) × (Fin q → Fin D → Bool) :=
  let S := fixedObservedColumns ω.1 ω.2
  let b := fun j => decide (initialIndex ∈ S j)
  (b, runReplies (fun S hist j => decide (ask b hist ∈ S j)) S [] q)

theorem initializedTableRun_eq {n D k : ℕ} (initialIndex : Fin n)
    (ask : (Fin D → Bool) → List (Fin D → Bool) → Fin n) (q : ℕ)
    (ω : FixedTableSample n D k) :
    (fixedTableTranscript (initializedAsk initialIndex ask) [] (q + 1) ω).2 =
      Fin.cons (initializedTableRun initialIndex ask q ω).1 (initializedTableRun initialIndex ask q ω).2 := by
  exact initializedAsk_run initialIndex ask
    (fun (S : Fin D → Finset (Fin n)) i j => decide (i ∈ S j)) (fixedObservedColumns ω.1 ω.2) q

def initializedAlignmentEvent {n D k : ℕ} {κ : Type*} (initialIndex : Fin n)
    (ask : (Fin D → Bool) → List (Fin D → Bool) → Fin n) (q : ℕ)
    (w : (Fin D → Bool) → (Fin q → Fin D → Bool) → κ → EuclideanSpace ℝ (Fin D)) (a : ℝ) :
    Set (FixedTableSample n D k) := {ω | ∃ l, a ≤ ⟪sampledDirection ω,
      w (initializedTableRun initialIndex ask q ω).1 (initializedTableRun initialIndex ask q ω).2 l⟫_ℝ}

theorem initializedAlignmentEvent_eq {n D k : ℕ} {κ : Type*} (initialIndex : Fin n)
    (ask : (Fin D → Bool) → List (Fin D → Bool) → Fin n) (q : ℕ)
    (w : (Fin D → Bool) → (Fin q → Fin D → Bool) → κ → EuclideanSpace ℝ (Fin D)) (a : ℝ) :
    (initializedAlignmentEvent initialIndex ask q w a : Set (FixedTableSample n D k)) =
      tableAlignmentEvent (initializedAsk initialIndex ask) [] (q + 1)
        (fun v => w (v 0) (Fin.tail v)) a := by
  ext ω
  simp only [initializedAlignmentEvent, tableAlignmentEvent, Set.mem_setOf_eq,
    initializedTableRun_eq, Fin.cons_zero, Fin.tail_cons]

theorem initialized_row_alignment_quarter {n D k : ℕ} {κ : Type*} [Fintype κ]
    (hn : 0 < n) (hD : 0 < D) (hk : k ≤ n)
    (m : ℝ) (hm : 0 ≤ m) (hbalance : 2 * (k : ℝ) = n + m)
    (initialIndex : Fin n) (ask : (Fin D → Bool) → List (Fin D → Bool) → Fin n)
    (q : ℕ) (hbudget : 8 * m + 9 * (q + 1 : ℕ) ≤ n)
    (w : (Fin D → Bool) → (Fin q → Fin D → Bool) → κ → EuclideanSpace ℝ (Fin D))
    (hw : ∀ b v l, ‖w b v l‖ ≤ 1) (a : ℝ) (ha : 0 < a)
    (hqueries : (q + 1 : ℕ) * (m / n) ^ 2 ≤ a ^ 2 / 1024)
    (hdim : 32 * Real.log 2 ≤ a ^ 2 * D)
    (hfamily : (Fintype.card κ : ℝ) ≤ Real.exp (a ^ 2 * D / 4)) :
    ((fixedTableLaw n D k hk).toOuterMeasure (initializedAlignmentEvent initialIndex ask q w a)).toReal ≤ 1 / 4 := by
  rw [initializedAlignmentEvent_eq]
  exact fixedTable_alignment_quarter hn hD hk m hm hbalance _ [] (q + 1) hbudget
    (fun v => w (v 0) (Fin.tail v)) (fun v l => hw _ _ l) a ha hqueries hdim hfamily

theorem initialized_row_cost_lower {n D k : ℕ} {κ : Type*} [Fintype κ]
    (hn : 0 < n) (hD : 0 < D) (hk : k ≤ n)
    (m : ℝ) (hm : 0 < m) (hmn : m ≤ (n : ℝ) / 16) (hbalance : 2 * (k : ℝ) = n + m)
    (initialIndex : Fin n) (ask : (Fin D → Bool) → List (Fin D → Bool) → Fin n) (q : ℕ)
    (w : (Fin D → Bool) → (Fin q → Fin D → Bool) → κ → EuclideanSpace ℝ (Fin D))
    (hw : ∀ b v l, ‖w b v l‖ ≤ 1) (a : ℝ) (ha : 0 < a)
    (hdim : 32 * Real.log 2 ≤ a ^ 2 * D)
    (hfamily : (Fintype.card κ : ℝ) ≤ Real.exp (a ^ 2 * D / 4))
    (hsuccess : 1 / 2 ≤ ((fixedTableLaw n D k hk).toOuterMeasure
      (initializedAlignmentEvent initialIndex ask q w a)).toReal) :
    min ((n : ℝ) / 18) (a ^ 2 / (1024 * (m / n) ^ 2)) - 1 < q := by
  rw [initializedAlignmentEvent_eq] at hsuccess
  have h := fixedTable_row_cost_lower hn hD hk m hm hmn hbalance (initializedAsk initialIndex ask)
    [] (q + 1) (fun v => w (v 0) (Fin.tail v)) (fun v l => hw _ _ l) a ha hdim hfamily hsuccess
  push_cast at h
  linarith

/-- The initialization index and the subsequent strategy may both depend on
arbitrary independent side information and private randomness. -/
theorem randomized_initialized_alignment_quarter {Ω : Type*} [MeasurableSpace Ω]
    {n D k : ℕ} {κ : Type*} [Fintype κ]
    (P : Measure Ω) [IsProbabilityMeasure P] (hn : 0 < n) (hD : 0 < D) (hk : k ≤ n)
    (m : ℝ) (hm : 0 ≤ m) (hbalance : 2 * (k : ℝ) = n + m)
    (initialIndex : Ω → Fin n) (ask : Ω → (Fin D → Bool) → List (Fin D → Bool) → Fin n)
    (q : ℕ) (hbudget : 8 * m + 9 * (q + 1 : ℕ) ≤ n)
    (w : Ω → (Fin D → Bool) → (Fin q → Fin D → Bool) → κ → EuclideanSpace ℝ (Fin D))
    (hw : ∀ s b v l, ‖w s b v l‖ ≤ 1) (a : ℝ) (ha : 0 < a)
    (hqueries : (q + 1 : ℕ) * (m / n) ^ 2 ≤ a ^ 2 / 1024)
    (hdim : 32 * Real.log 2 ≤ a ^ 2 * D)
    (hfamily : (Fintype.card κ : ℝ) ≤ Real.exp (a ^ 2 * D / 4))
    (hmeas : ∀ ω : FixedTableSample n D k, MeasurableSet
      {s | ω ∈ initializedAlignmentEvent (initialIndex s) (ask s) q (w s) a}) :
    ∑ ω, (fixedTableLaw n D k hk ω).toReal * P.real
      {s | ω ∈ initializedAlignmentEvent (initialIndex s) (ask s) q (w s) a} ≤ 1 / 4 := by
  apply pmf_seed_event_average_le P (fixedTableLaw n D k hk) _ hmeas
  intro s
  exact initialized_row_alignment_quarter hn hD hk m hm hbalance (initialIndex s) (ask s) q hbudget
    (w s) (hw s) a ha hqueries hdim hfamily

end FullJet
