import MatchingBounds1005.CUPGPhaseReplies

/-! Ordered response-only minimization matching the analytic candidate list. -/
noncomputable section
open MeasureTheory

namespace MatchingBounds1005.CUPG

def bestReplyList {E : Type*} (initial : E × ℝ) : List (E × ℝ) → E × ℝ
  | [] => initial
  | x :: xs => chooseLowerReply x (bestReplyList initial xs)

theorem bestReplyList_correct {E : Type*} (f : E → ℝ) (start : E) (xs : List E) :
    bestReplyList (start, f start) (xs.map (fun x => (x, f x))) =
      (bestPoint f start xs, f (bestPoint f start xs)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, bestReplyList, ih, chooseLowerReply_correct, bestPoint]

theorem measurable_bestReplyList_functions {X E : Type*} [MeasurableSpace X] [MeasurableSpace E]
    (initial : X → E × ℝ) (fs : List (X → E × ℝ)) (hi : Measurable initial)
    (hfs : ∀ F ∈ fs, Measurable F) :
    Measurable (fun p => bestReplyList (initial p) (fs.map (fun F => F p))) := by
  induction fs with
  | nil => exact hi
  | cons F fs ih =>
    have hF := hfs F (by simp)
    have ht := ih (fun G hG => hfs G (by simp [hG]))
    exact chooseLowerReply_measurable.comp (hF.prodMk ht)

def rawRecord {d : ℕ} (q α τ L ε : ℝ) (N t : ℕ) (p : PhaseData d) : Model.Space d × ℝ :=
  (rawBodyQuery q α τ L ε N t p, (p.2 t).1)

@[fun_prop] theorem measurable_rawRecord {d : ℕ} (q α τ L ε : ℝ) (N t : ℕ) :
    Measurable (rawRecord (d := d) q α τ L ε N t) :=
  (measurable_rawBodyQuery q α τ L ε N t).prodMk
    (((measurable_pi_apply t).comp measurable_snd).fst)

def rawWitnessRecord {d : ℕ} (q α : ℝ) (p : PhaseData d) (n : ℕ) : Model.Space d × ℝ :=
  if (rawProxY q α p n).1 ≤ (p.2 0).1 then (rawZ q α p n, (rawZReply p n).1)
    else (p.1, (p.2 0).1)

@[fun_prop] theorem measurable_rawWitnessRecord {d : ℕ} (q α : ℝ) (n : ℕ) :
    Measurable (fun p : PhaseData d => rawWitnessRecord q α p n) := by
  apply Measurable.ite
  · exact measurableSet_le (continuous_rawProxY q α n).fst.measurable
      (((continuous_apply 0).comp continuous_snd).fst.measurable)
  · exact (continuous_rawZ q α n).measurable.prodMk (continuous_rawZReply n).fst.measurable
  · exact measurable_fst.prodMk (((measurable_pi_apply 0).comp measurable_snd).fst)

def rawCandidateMaps {d : ℕ} (q α τ L ε : ℝ) (N : ℕ) : List (PhaseData d → Model.Space d × ℝ) :=
  [fun p => rawWitnessRecord q α p (rawStop q α L ε N p)] ++
    (List.range (N + 1)).map (fun j => rawRecord q α τ L ε N (3 * j)) ++
    (List.range N).map (fun j => rawRecord q α τ L ε N (3 * N + 2 + 2 * j)) ++
    (List.range N).map (fun j => rawRecord q α τ L ε N (3 * N + 3 + 2 * j)) ++
    (List.range N).map (fun j => rawRecord q α τ L ε N (5 * N + 2 + 4 * j)) ++
    (List.range N).map (fun j => rawRecord q α τ L ε N (5 * N + 3 + 4 * j)) ++
    (List.range N).map (fun j => rawRecord q α τ L ε N (5 * N + 4 + 4 * j)) ++
    (List.range N).map (fun j => rawRecord q α τ L ε N (5 * N + 5 + 4 * j))

theorem rawCandidateMaps_measurable {d : ℕ} (q α τ L ε : ℝ) (N : ℕ) :
    ∀ F ∈ rawCandidateMaps (d := d) q α τ L ε N, Measurable F := by
  have hw : Measurable (fun p : PhaseData d => rawWitnessRecord q α p (rawStop q α L ε N p)) :=
    measurable_nat_evaluation _ (measurable_rawWitnessRecord q α) _ (measurable_rawStop q α L ε N)
  intro F hF
  simp only [rawCandidateMaps, List.mem_append, List.mem_singleton, List.mem_map] at hF
  rcases hF with (((((((hF | hF) | hF) | hF) | hF) | hF) | hF) | hF)
  · subst F; exact hw
  all_goals obtain ⟨j, _, rfl⟩ := hF
  all_goals exact measurable_rawRecord q α τ L ε N _

def rawOrderedCandidate {d : ℕ} (q α τ L ε : ℝ) (N : ℕ) (p : PhaseData d) : Model.Space d := by
  classical
  exact if RawPass q α L p (rawStop q α L ε N p) then rawY q α p (rawStop q α L ε N p)
  else (bestReplyList (p.1, (p.2 0).1)
    ((rawCandidateMaps q α τ L ε N).map (fun F => F p))).1

@[fun_prop] theorem measurable_rawOrderedCandidate {d : ℕ} (q α τ L ε : ℝ) (N : ℕ) :
    Measurable (rawOrderedCandidate (d := d) q α τ L ε N) := by
  unfold rawOrderedCandidate
  apply Measurable.ite
  · exact measurableSet_nat_choice _ (measurableSet_rawPass q α L) (measurable_rawStop q α L ε N)
  · exact measurable_nat_evaluation _ (fun n => (continuous_rawY q α n).measurable) _
      (measurable_rawStop q α L ε N)
  · exact (measurable_bestReplyList_functions _ _
      (measurable_fst.prodMk (((measurable_pi_apply 0).comp measurable_snd).fst))
      (rawCandidateMaps_measurable q α τ L ε N)).fst

def rawOrderedPhaseQuery {d : ℕ} (q α τ L ε : ℝ) (N t : ℕ) (p : PhaseData d) : Model.Space d :=
  if t < 9 * N + 2 then rawBodyQuery q α τ L ε N t p else rawOrderedCandidate q α τ L ε N p

@[fun_prop] theorem measurable_rawOrderedPhaseQuery {d : ℕ} (q α τ L ε : ℝ) (N t : ℕ) :
    Measurable (rawOrderedPhaseQuery (d := d) q α τ L ε N t) := by
  unfold rawOrderedPhaseQuery
  split_ifs
  · exact measurable_rawBodyQuery q α τ L ε N t
  · exact measurable_rawOrderedCandidate q α τ L ε N

end MatchingBounds1005.CUPG
