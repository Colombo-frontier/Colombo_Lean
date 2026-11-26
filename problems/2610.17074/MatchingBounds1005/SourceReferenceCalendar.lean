import MatchingBounds1005.SourceReferenceProgram
import MatchingBounds1005.AccessibleCalendar
import MatchingBounds1005.SourcePowerGeometry
import MatchingBounds1005.CandidateCalendar

/-! Eligibility and exact command counts of the actual accessible reference
program. Each readout is disclosed at most once, at its prescribed layer. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace MatchingBounds1005.ReadoutCalendar
open GaussianVector ScheduledHaar AccessibleReferenceCompiler
universe u
variable {S : Type u} [MeasurableSpace S] {d N : ℕ}

theorem prependMachine_columnsAt (I : ℕ → Submodule ℝ (Vec d))
    (b : Fin N → Vec d) (update : Fin N → Update (E := Vec d) S)
    (xs : List (Fin N)) (w : List SourceKind) (M : Machine (E := Vec d) (S := S) w)
    (start : ℕ) (hb : ∀ i ∈ xs, b i ∈ I start) (hM : ColumnsAt I w M start) :
    ColumnsAt I (prependKinds xs w) (prependMachine b update xs w M) start := by
  induction xs with
  | nil => exact hM
  | cons i xs ih =>
      exact ⟨hb i (by simp), ih (fun j hj => hb j (by simp [hj]))⟩

theorem machine_columnsAt (I : ℕ → Submodule ℝ (Vec d))
    (b : Fin N → Vec d) (τ : Fin N → ℕ)
    (update : Fin N → Update (E := Vec d) S)
    (query candidate : ℕ → PhysicalRequest (E := Vec d) S × Update (E := Vec d) S)
    (hb : ∀ i, b i ∈ I (τ i)) (start rounds : ℕ) :
    ColumnsAt I (kinds τ start rounds) (machine b τ update query candidate start rounds) start := by
  induction rounds generalizing start with
  | zero => trivial
  | succ rounds ih =>
      apply prependMachine_columnsAt
      · intro i hi
        have he := (VisibleReadouts.mem_due τ start i).mp hi
        rw [← he]
        exact hb i
      · exact ih (start + 1)

theorem commandCount_prepend (kind : SourceKind) (xs : List (Fin N)) (w : List SourceKind) :
    commandCount kind (prependKinds xs w) =
      (if kind = .disclose then xs.length else 0) + commandCount kind w := by
  induction xs with
  | nil => simp [prependKinds]
  | cons i xs ih =>
      cases kind <;> simp [prependKinds, commandCount, prependKinds] at ih ⊢ <;> omega

theorem query_count (τ : Fin N → ℕ) (start rounds : ℕ) :
    commandCount .query (kinds τ start rounds) = rounds := by
  induction rounds generalizing start with
  | zero => simp [kinds, commandCount]
  | succ rounds ih =>
      rw [kinds, commandCount_prepend]
      simp [commandCount, ih, Nat.add_comm]

theorem candidate_count (τ : Fin N → ℕ) (start rounds : ℕ) :
    commandCount .candidate (kinds τ start rounds) = 1 := by
  induction rounds generalizing start with
  | zero => simp [kinds, commandCount]
  | succ rounds ih =>
      rw [kinds, commandCount_prepend]
      simp [commandCount, ih]

theorem due_length (τ : Fin N → ℕ) (start : ℕ) :
    (VisibleReadouts.due τ start).length = ∑ i : Fin N, if τ i = start then 1 else 0 := by
  classical
  rw [VisibleReadouts.due, Finset.length_toList]
  exact Finset.card_filter _ _

theorem disclosure_count_exact (τ : Fin N → ℕ) (start rounds : ℕ) :
    commandCount .disclose (kinds τ start rounds) =
      ∑ i : Fin N, if start ≤ τ i ∧ τ i < start + rounds then 1 else 0 := by
  classical
  induction rounds generalizing start with
  | zero =>
      simp only [kinds, commandCount, reduceCtorEq, if_false, Nat.add_zero, zero_add]
      symm
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg (by omega)]
  | succ rounds ih =>
      rw [kinds, commandCount_prepend]
      simp only [if_pos rfl, commandCount,
        show SourceKind.query ≠ SourceKind.disclose by decide, if_false, if_true, zero_add]
      rw [ih, due_length, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases he : τ i = start
      · simp [he]
      · by_cases hrange : start + 1 ≤ τ i ∧ τ i < start + 1 + rounds
        · have hbig : start ≤ τ i ∧ τ i < start + (rounds + 1) := by omega
          simp [he, hrange, hbig]
        · have hbig : ¬(start ≤ τ i ∧ τ i < start + (rounds + 1)) := by omega
          simp [he, hrange, hbig]

theorem disclosure_count_le (τ : Fin N → ℕ) (start rounds : ℕ) :
    commandCount .disclose (kinds τ start rounds) ≤ N := by
  rw [disclosure_count_exact]
  calc
    _ ≤ ∑ _i : Fin N, 1 := Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
    _ = _ := by simp

end MatchingBounds1005.ReadoutCalendar

namespace MatchingBounds1005.SourceReferenceProgram
open GaussianVector ScheduledHaar AccessibleReferenceCompiler
variable {Seed : Type} [MeasurableSpace Seed] {d N H : ℕ}

theorem plan_columnsAt (P : Parameters d N) (A : Model.Algorithm d Seed)
    (I : ℕ → Submodule ℝ (Vec d)) (hc : P.c ∈ I 1)
    (hb : ∀ i, P.b i ∈ I (P.disclosure i)) :
    (plan (H := H) P A).ColumnsAt I (commands P H) 1 := by
  apply compile_columnsAt
  exact ⟨hc, ReadoutCalendar.machine_columnsAt I P.b P.disclosure _ _ _ hb 1 H⟩

theorem plan_scheduled (P : Parameters d N) (A : Model.Algorithm d Seed)
    (I : ℕ → Submodule ℝ (Vec d)) (hc : P.c ∈ I 1)
    (hb : ∀ i, P.b i ∈ I (P.disclosure i))
    (hQI : ∀ t, (I t).map P.Q.toLinearMap ≤ I (t + 1)) :
    (plan (H := H) P A).Scheduled P.Q (commands P H)
      (fun j => I (commandClock (commands P H) 1 j)) :=
  SourcePolicy.scheduled_of_calendar (commands P H) (plan P A) P.Q I hQI 1
    (plan_columnsAt P A I hc hb)

theorem commands_queries (P : Parameters d N) (H : ℕ) :
    commandCount .query (commands P H) = H := by
  simp [commands, commandCount, ReadoutCalendar.query_count]

theorem commands_candidates (P : Parameters d N) (H : ℕ) :
    commandCount .candidate (commands P H) = 1 := by
  simp [commands, commandCount, ReadoutCalendar.candidate_count]

theorem commands_disclosures (P : Parameters d N) (H : ℕ) :
    commandCount .disclose (commands P H) ≤ N + 1 := by
  have h := ReadoutCalendar.disclosure_count_le P.disclosure 1 H
  simp only [commands, commandCount, if_pos rfl, if_true]
  omega

theorem independent_start_count (P : Parameters d N) (H : ℕ) :
    actionCount (commands P H).length + actionCount (commands P H).length ≤ 6 * (N + H + 2) := by
  have h := source_start_budget (commands P H) (N + 1) H (commands_disclosures P H)
    (commands_queries P H).le (commands_candidates P H).le
  omega

theorem bounded_start_count (P : Parameters d N) (H D : ℕ)
    (hN : N + 1 ≤ D) (hH : H ≤ D) :
    actionCount (commands P H).length + actionCount (commands P H).length ≤ 12 * D + 6 := by
  have h := independent_start_count P H
  omega

end MatchingBounds1005.SourceReferenceProgram

namespace MatchingBounds1005.AnalyticFamily
open EpsilonCalibration PathGreen

theorem readout_count_le_baseSize (p : ℕ) (t : ℝ) (ht : 0 < t) (hp : t ≤ parameterThreshold p) :
    phaseCount (amplitudeConstant p) t + 1 ≤ baseSize p t := by
  have hN := phase_pos p ht hp
  have hM := ceiling_scale _ (pathScale_pos _ _ _ (amplitudeConstant_pos p) (scale_pos p) ht)
    (path_small p ht hp)
  have hm : 2 ≤ pathSize (pathScale (amplitudeConstant p) (scale p) t) := by omega
  have hmul := Nat.mul_le_mul_left (phaseCount (amplitudeConstant p) t) hm
  unfold baseSize
  omega

theorem actual_reference_start_count (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ candidateThreshold p)
    (P : SourceReferenceProgram.Parameters (dimension p t (powerCopies t))
      (phaseCount (amplitudeConstant p) t)) :
    let w := SourceReferenceProgram.commands P (candidateBudget p t)
    ScheduledHaar.actionCount w.length + ScheduledHaar.actionCount w.length ≤ maximalStarts p t := by
  have hc := SourceReferenceProgram.independent_start_count P (candidateBudget p t)
  have hN := readout_count_le_baseSize p t ht (hsmall.trans (min_le_left _ _))
  have hT := candidateBudget_le_baseSize p t ht hsmall
  change candidateBudget p t ≤ baseSize p t at hT
  change _ ≤ 12 * baseSize p t + 6
  omega

theorem actual_reference_start_count_native (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ candidateThreshold p)
    (P : SourceReferenceProgram.Parameters (dimension p t (powerCopies t))
      (phaseCount (amplitudeConstant p) t - 1 + 1)) :
    let w := SourceReferenceProgram.commands P (candidateBudget p t)
    ScheduledHaar.actionCount w.length + ScheduledHaar.actionCount w.length ≤ maximalStarts p t := by
  have hp := hsmall.trans (min_le_left _ _)
  have hphase := phase_pos p ht hp
  have hN := readout_count_le_baseSize p t ht hp
  have hT := candidateBudget_le_baseSize p t ht hsmall
  exact SourceReferenceProgram.bounded_start_count P _ (baseSize p t) (by omega) hT

end MatchingBounds1005.AnalyticFamily
