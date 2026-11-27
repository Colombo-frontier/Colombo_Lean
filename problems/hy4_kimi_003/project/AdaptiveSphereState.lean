import AdaptiveSphereResidualFrame
import AdaptiveSphereInverse
import AdaptiveSphereMeasurable

/-! Actual finite rank/frame recursion driven by counterfactual scalar histories.
The frame before and immediately after a query is measurable in the OLD past.
-/

open MeasureTheory Set
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereState

open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereFrame
open Task006.AdaptiveSphereResidualFrame Task006.AdaptiveSphereTranscript
open Task006.AdaptiveSphereMeasurable

noncomputable section

abbrev FrameState (d : ℕ) := Fin (d+1) × OrthogonalGroup d

variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

def initialState (d : ℕ) : FrameState d := (⟨0, by omega⟩, 1)

def residualUpdate (r : Fin d) (B : OrthogonalGroup d) (q : E d) : OrthogonalGroup d :=
  B * fullResidualStep r (action B⁻¹ q)

theorem measurable_residualUpdate (r : Fin d) :
    Measurable (fun p : OrthogonalGroup d × E d => residualUpdate r p.1 p.2) := by
  have hcoords : Measurable (fun p : OrthogonalGroup d × E d => action p.1⁻¹ p.2) :=
    orthogonal_inverse_action_measurable
  have hsecond : Measurable (fun p : OrthogonalGroup d × E d =>
      fullResidualStep r (action p.1⁻¹ p.2)) := (measurable_fullResidualStep r).comp hcoords
  have hpair : Measurable (fun p : OrthogonalGroup d × E d =>
      (p.1, fullResidualStep r (action p.1⁻¹ p.2))) := measurable_fst.prodMk hsecond
  have hmul : Measurable
      (fun p : OrthogonalGroup d × OrthogonalGroup d => p.1 * p.2) := measurable_mul
  have hresult := hmul.comp hpair
  simpa only [residualUpdate, Function.comp_def] using hresult

/-- Stop rank acquisition at k, but no sample or objective guarantee is assumed. -/
def stateStep (k : ℕ) (hkd : k ≤ d) (state : FrameState d) (q : E d) : FrameState d :=
  if hr : state.1.val < k then
    let pivot : Fin d := ⟨state.1.val, by omega⟩
    if residualCoordinates pivot.val (Nat.le_of_lt pivot.isLt) (action state.2⁻¹ q) = 0 then
      state
    else (⟨state.1.val + 1, by omega⟩, residualUpdate pivot state.2 q)
  else state

/-- All finite-rank branches of the actual update are Borel. -/
theorem measurable_stateStep (k : ℕ) (hkd : k ≤ d) :
    Measurable (fun p : FrameState d × E d => stateStep k hkd p.1 p.2) := by
  have hfixed (rank : Fin (d+1)) : Measurable
      (fun p : OrthogonalGroup d × E d => stateStep k hkd (rank,p.1) p.2) := by
    by_cases hr : rank.val < k
    · let pivot : Fin d := ⟨rank.val, by omega⟩
      have hcoords : Measurable (fun p : OrthogonalGroup d × E d => action p.1⁻¹ p.2) :=
        orthogonal_inverse_action_measurable
      have hres : Measurable (fun p : OrthogonalGroup d × E d =>
          residualCoordinates pivot.val (Nat.le_of_lt pivot.isLt) (action p.1⁻¹ p.2)) :=
        (continuous_residualCoordinates pivot.val (Nat.le_of_lt pivot.isLt)).measurable.comp hcoords
      have hcase : Measurable (fun p : OrthogonalGroup d × E d =>
          if residualCoordinates pivot.val (Nat.le_of_lt pivot.isLt) (action p.1⁻¹ p.2) = 0 then
            ((rank,p.1) : FrameState d)
          else ((⟨rank.val+1, by omega⟩, residualUpdate pivot p.1 p.2) : FrameState d)) :=
        Measurable.ite (hres (measurableSet_singleton 0))
          (measurable_const.prodMk measurable_fst)
          (measurable_const.prodMk (measurable_residualUpdate pivot))
      simpa only [stateStep, dif_pos hr] using hcase
    · simpa only [stateStep, dif_neg hr] using
        (measurable_const.prodMk measurable_fst :
          Measurable (fun p : OrthogonalGroup d × E d => ((rank,p.1) : FrameState d)))
  have hall : Measurable (fun p : Fin (d+1) × (OrthogonalGroup d × E d) =>
      stateStep k hkd (p.1,p.2.1) p.2.2) :=
    measurable_from_prod_countable_right hfixed
  have hreorder : Measurable (fun p : FrameState d × E d => (p.1.1,(p.1.2,p.2))) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  exact hall.comp hreorder

/-- Deterministic one-step rank bookkeeping. -/
theorem stateStep_rank_bounds (k : ℕ) (hkd : k ≤ d) (state : FrameState d) (q : E d)
    (hr : state.1.val ≤ k) :
    state.1.val ≤ (stateStep k hkd state q).1.val ∧
      (stateStep k hkd state q).1.val ≤ min k (state.1.val+1) := by
  by_cases hpre : state.1.val < k
  · rw [stateStep, dif_pos hpre]
    dsimp only
    split_ifs
    · change state.1.val ≤ state.1.val ∧ state.1.val ≤ min k (state.1.val+1)
      omega
    · change state.1.val ≤ state.1.val+1 ∧ state.1.val+1 ≤ min k (state.1.val+1)
      omega
  · rw [stateStep, dif_neg hpre]
    change state.1.val ≤ state.1.val ∧ state.1.val ≤ min k (state.1.val+1)
    omega

/-- A counterfactual frame/rank is computed solely from the supplied scalar history. -/
def frameFromTranscript (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) : ℕ → Transcript N → FrameState d
  | 0, _ => initialState d
  | t+1, h =>
    if ht : t < N then
      stateStep k hkd (frameFromTranscript A weight tape seed k hkd t h)
        (effectiveVector weight tape (A.action ⟨t, ht⟩ seed h))
    else frameFromTranscript A weight tape seed k hkd t h

theorem measurable_frameFromTranscript (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) :
    Measurable (frameFromTranscript A weight tape seed k hkd t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    by_cases ht : t < N
    · have hinput : Measurable (fun h : Transcript N =>
          (seed,h)) := measurable_const.prodMk measurable_id
      have hquery : Measurable (fun h : Transcript N =>
          effectiveVector weight tape (A.action ⟨t, ht⟩ seed h)) :=
        (measurable_effectiveVector weight tape).comp ((A.action_measurable ⟨t,ht⟩).comp hinput)
      have hresult := (measurable_stateStep k hkd).comp (ih.prodMk hquery)
      simpa only [frameFromTranscript, dif_pos ht, Function.comp_def] using hresult
    · simpa only [frameFromTranscript, dif_neg ht] using ih

/-- The complete frame state before slot t depends only on earlier scalar replies. -/
theorem frameFromTranscript_past_only (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (h h' : Transcript N) (hpast : ∀ i, i.val < t → h i = h' i) :
    frameFromTranscript A weight tape seed k hkd t h =
      frameFromTranscript A weight tape seed k hkd t h' := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hprev := ih (fun i hi => hpast i (by omega))
    rw [frameFromTranscript, frameFromTranscript]
    split_ifs with ht
    · rw [hprev, A.past_only ⟨t, ht⟩ seed h h' (fun i hi => hpast i (Nat.lt_trans hi (Nat.lt_succ_self t)))]
    · exact hprev

/-- Even the frame AFTER choosing the next vector is determined BEFORE its reply. -/
theorem frameFromTranscript_succ_old_past_only (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (h h' : Transcript N) (hpast : ∀ i, i.val < t → h i = h' i) :
    frameFromTranscript A weight tape seed k hkd (t+1) h =
      frameFromTranscript A weight tape seed k hkd (t+1) h' := by
  rw [frameFromTranscript, frameFromTranscript]
  split_ifs with ht
  · rw [frameFromTranscript_past_only A weight tape seed k hkd t h h' hpast,
      A.past_only ⟨t, ht⟩ seed h h' hpast]
  · exact frameFromTranscript_past_only A weight tape seed k hkd t h h' hpast

/-- Rank acquisition remains stopped at k on every counterfactual path. -/
theorem frameFromTranscript_rank_cap (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (h : Transcript N) :
    (frameFromTranscript A weight tape seed k hkd t h).1.val ≤ k := by
  induction t with
  | zero => simp [frameFromTranscript, initialState]
  | succ t ih =>
    rw [frameFromTranscript]
    split_ifs with ht
    · exact ((stateStep_rank_bounds k hkd _ _ ih).2).trans (Nat.min_le_left _ _)
    · exact ih

@[simp] theorem residualCoordinates_zero (r : ℕ) (hr : r ≤ d) :
    residualCoordinates r hr (0 : E d) = 0 := by
  apply WithLp.ofLp_injective 2
  funext i
  rfl

/-- An uninformative zero measurement never acquires rank. -/
theorem stateStep_zero (k : ℕ) (hkd : k ≤ d) (state : FrameState d) :
    stateStep k hkd state (0 : E d) = state := by
  by_cases hpre : state.1.val < k
  · simp [stateStep, hpre, residualCoordinates_zero]
  · simp only [stateStep, dif_neg hpre]

/-- Each informative measurement contributes at most one rank increment. -/
theorem stateStep_rank_indicator (k : ℕ) (hkd : k ≤ d)
    (state : FrameState d) (q : E d) (hr : state.1.val ≤ k) :
    (stateStep k hkd state q).1.val ≤ state.1.val + (if q = 0 then 0 else 1) := by
  by_cases hq : q = 0
  · subst q
    simp [stateStep_zero]
  · rw [if_neg hq]
    exact ((stateStep_rank_bounds k hkd state q hr).2).trans (Nat.min_le_right _ _)

#print axioms measurable_stateStep
#print axioms stateStep_rank_bounds
#print axioms measurable_frameFromTranscript
#print axioms frameFromTranscript_past_only
#print axioms frameFromTranscript_succ_old_past_only
#print axioms frameFromTranscript_rank_cap
#print axioms stateStep_zero
#print axioms stateStep_rank_indicator

end
end Task006.AdaptiveSphereState
