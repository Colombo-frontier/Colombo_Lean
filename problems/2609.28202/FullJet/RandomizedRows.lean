import FullJet.FixedTableTranscript
import FullJet.IndependentSeed

open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace FullJet

def tableAlignmentEvent {n D k : ℕ} {κ : Type*}
    (ask : List (Fin D → Bool) → Fin n) (past : List (Fin D → Bool)) (q : ℕ)
    (w : (Fin q → Fin D → Bool) → κ → EuclideanSpace ℝ (Fin D)) (a : ℝ) :
    Set (FixedTableSample n D k) :=
  {ω | ∃ l, a ≤ ⟪sampledDirection ω, w (fixedTableTranscript ask past q ω).2 l⟫_ℝ}

theorem fixedTable_alignment_quarter {n D k : ℕ} {κ : Type*} [Fintype κ]
    (hn : 0 < n) (hD : 0 < D) (hk : k ≤ n)
    (m : ℝ) (hm : 0 ≤ m) (hbalance : 2 * (k : ℝ) = n + m)
    (ask : List (Fin D → Bool) → Fin n) (past : List (Fin D → Bool))
    (q : ℕ) (hbudget : 8 * m + 9 * (q : ℝ) ≤ n)
    (w : (Fin q → Fin D → Bool) → κ → EuclideanSpace ℝ (Fin D))
    (hw : ∀ v l, ‖w v l‖ ≤ 1) (a : ℝ) (ha : 0 < a)
    (hqueries : (q : ℝ) * (m / n) ^ 2 ≤ a ^ 2 / 1024)
    (hdim : 32 * Real.log 2 ≤ a ^ 2 * D)
    (hfamily : (Fintype.card κ : ℝ) ≤ Real.exp (a ^ 2 * D / 4)) :
    ((fixedTableLaw n D k hk).toOuterMeasure (tableAlignmentEvent ask past q w a)).toReal ≤ 1 / 4 := by
  unfold tableAlignmentEvent
  rw [fixedTable_alignment_probability_eq]
  exact adaptive_row_alignment_quarter hn hD k hk m hm hbalance ask past q hbudget
    w hw a ha hqueries hdim hfamily

def rowSeedAlignment {Ω : Type*} {n D k : ℕ} {κ : Type*}
    (ask : Ω → List (Fin D → Bool) → Fin n) (past : Ω → List (Fin D → Bool)) (q : ℕ)
    (w : Ω → (Fin q → Fin D → Bool) → κ → EuclideanSpace ℝ (Fin D)) (a : ℝ)
    (ω : FixedTableSample n D k) : Set Ω :=
  {s | ω ∈ tableAlignmentEvent (ask s) (past s) q (w s) a}

/-- Independent side information may contain arbitrary private randomness.
The resulting average bound uses the original hard-table distribution. -/
theorem randomized_row_alignment_quarter {Ω : Type*} [MeasurableSpace Ω]
    {n D k : ℕ} {κ : Type*} [Fintype κ]
    (P : Measure Ω) [IsProbabilityMeasure P] (hn : 0 < n) (hD : 0 < D) (hk : k ≤ n)
    (m : ℝ) (hm : 0 ≤ m) (hbalance : 2 * (k : ℝ) = n + m)
    (ask : Ω → List (Fin D → Bool) → Fin n) (past : Ω → List (Fin D → Bool))
    (q : ℕ) (hbudget : 8 * m + 9 * (q : ℝ) ≤ n)
    (w : Ω → (Fin q → Fin D → Bool) → κ → EuclideanSpace ℝ (Fin D))
    (hw : ∀ s v l, ‖w s v l‖ ≤ 1) (a : ℝ) (ha : 0 < a)
    (hqueries : (q : ℝ) * (m / n) ^ 2 ≤ a ^ 2 / 1024)
    (hdim : 32 * Real.log 2 ≤ a ^ 2 * D)
    (hfamily : (Fintype.card κ : ℝ) ≤ Real.exp (a ^ 2 * D / 4))
    (hmeas : ∀ ω : FixedTableSample n D k, MeasurableSet (rowSeedAlignment ask past q w a ω)) :
    ∑ ω, (fixedTableLaw n D k hk ω).toReal * P.real (rowSeedAlignment ask past q w a ω) ≤ 1 / 4 := by
  apply pmf_seed_event_average_le P (fixedTableLaw n D k hk) _ hmeas
  intro s
  exact fixedTable_alignment_quarter hn hD hk m hm hbalance (ask s) (past s) q hbudget
    (w s) (hw s) a ha hqueries hdim hfamily

/-- A single fixed original table defeats the randomized row strategy with
probability at least three quarters; no minimax principle is assumed. -/
theorem randomized_row_fixed_failure {Ω : Type*} [MeasurableSpace Ω]
    {n D k : ℕ} {κ : Type*} [Fintype κ]
    (P : Measure Ω) [IsProbabilityMeasure P] (hn : 0 < n) (hD : 0 < D) (hk : k ≤ n)
    (m : ℝ) (hm : 0 ≤ m) (hbalance : 2 * (k : ℝ) = n + m)
    (ask : Ω → List (Fin D → Bool) → Fin n) (past : Ω → List (Fin D → Bool))
    (q : ℕ) (hbudget : 8 * m + 9 * (q : ℝ) ≤ n)
    (w : Ω → (Fin q → Fin D → Bool) → κ → EuclideanSpace ℝ (Fin D))
    (hw : ∀ s v l, ‖w s v l‖ ≤ 1) (a : ℝ) (ha : 0 < a)
    (hqueries : (q : ℝ) * (m / n) ^ 2 ≤ a ^ 2 / 1024)
    (hdim : 32 * Real.log 2 ≤ a ^ 2 * D)
    (hfamily : (Fintype.card κ : ℝ) ≤ Real.exp (a ^ 2 * D / 4))
    (hmeas : ∀ ω : FixedTableSample n D k, MeasurableSet (rowSeedAlignment ask past q w a ω)) :
    ∃ ω : FixedTableSample n D k, 3 / 4 ≤ P.real (rowSeedAlignment ask past q w a ω)ᶜ := by
  have h := randomized_row_alignment_quarter P hn hD hk m hm hbalance ask past q hbudget
    w hw a ha hqueries hdim hfamily hmeas
  obtain ⟨ω, hω, hlo⟩ := pmf_exists_low_probability P (fixedTableLaw n D k hk) _ (1 / 4) h
  refine ⟨ω, ?_⟩
  rw [measureReal_compl (hmeas ω), measureReal_univ_eq_one]
  linarith

/-- Randomization and independent side information cannot improve the
explicit one-stage row cost when average alignment success is at least half. -/
theorem randomized_row_cost_lower {Ω : Type*} [MeasurableSpace Ω]
    {n D k : ℕ} {κ : Type*} [Fintype κ]
    (P : Measure Ω) [IsProbabilityMeasure P] (hn : 0 < n) (hD : 0 < D) (hk : k ≤ n)
    (m : ℝ) (hm : 0 < m) (hmn : m ≤ (n : ℝ) / 16) (hbalance : 2 * (k : ℝ) = n + m)
    (ask : Ω → List (Fin D → Bool) → Fin n) (past : Ω → List (Fin D → Bool)) (q : ℕ)
    (w : Ω → (Fin q → Fin D → Bool) → κ → EuclideanSpace ℝ (Fin D))
    (hw : ∀ s v l, ‖w s v l‖ ≤ 1) (a : ℝ) (ha : 0 < a)
    (hdim : 32 * Real.log 2 ≤ a ^ 2 * D)
    (hfamily : (Fintype.card κ : ℝ) ≤ Real.exp (a ^ 2 * D / 4))
    (hmeas : ∀ ω : FixedTableSample n D k, MeasurableSet (rowSeedAlignment ask past q w a ω))
    (hsuccess : 1 / 2 ≤ ∑ ω, (fixedTableLaw n D k hk ω).toReal *
      P.real (rowSeedAlignment ask past q w a ω)) :
    min ((n : ℝ) / 18) (a ^ 2 / (1024 * (m / n) ^ 2)) < q := by
  by_contra h
  have hq := le_of_not_gt h
  have hqN := hq.trans (min_le_left _ _)
  have hqM := hq.trans (min_le_right _ _)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hbudget : 8 * m + 9 * (q : ℝ) ≤ n := by linarith
  have hden : 0 < 1024 * (m / n) ^ 2 := by positivity
  have hqueries : (q : ℝ) * (m / n) ^ 2 ≤ a ^ 2 / 1024 := by
    have hmul := (le_div_iff₀ hden).mp hqM
    nlinarith
  have hfail := randomized_row_alignment_quarter P hn hD hk m hm.le hbalance ask past q hbudget
    w hw a ha hqueries hdim hfamily hmeas
  linarith

end FullJet
