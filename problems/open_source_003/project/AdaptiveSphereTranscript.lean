import ModelFull

/-!
Exact affine fibers of the actual finite adaptive oracle execution.
This file proves a deterministic transcript identity for every query policy;
it does not identify a regular conditional distribution with the uniform law
on those fibers. That probabilistic step is separate.
-/

open MeasureTheory

namespace Task006.AdaptiveSphereTranscript

noncomputable section

open Task006.Full Task006.Full.OracleAlgorithm

variable {d N : ℕ} {S Ω Ω' : Type*} [MeasurableSpace S]

/-- A later update does not alter a different transcript coordinate. -/
theorem runPrefix_succ_apply_of_ne
    (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (t : ℕ) (i : Fin N) (hne : i.val ≠ t) :
    A.runPrefix F tape seed (t + 1) i = A.runPrefix F tape seed t i := by
  rw [runPrefix]
  split_ifs with ht
  · apply Function.update_of_ne
    intro h
    exact hne (congrArg Fin.val h)
  · rfl

/-- Already observed values are never overwritten. -/
theorem runPrefix_coordinate_stable
    (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (t u : ℕ) (htu : t ≤ u)
    (i : Fin N) (hi : i.val < t) :
    A.runPrefix F tape seed u i = A.runPrefix F tape seed t i := by
  induction u generalizing t with
  | zero =>
    have ht : t = 0 := by omega
    subst t
    rfl
  | succ u ih =>
    by_cases htu' : t ≤ u
    · calc
        A.runPrefix F tape seed (u + 1) i = A.runPrefix F tape seed u i :=
          runPrefix_succ_apply_of_ne A F tape seed u i (by omega)
        _ = A.runPrefix F tape seed t i := ih t htu' hi
    · have ht : t = u + 1 := by omega
      subst t
      rfl

/-- Future entries carry no hidden information: they are still zero. -/
theorem runPrefix_future_zero
    (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (t : ℕ) (i : Fin N) (hi : t ≤ i.val) :
    A.runPrefix F tape seed t i = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [runPrefix_succ_apply_of_ne A F tape seed t i (by omega)]
    exact ih (by omega)

/-- A complete transcript determines every prefix of the execution. -/
theorem runPrefix_eq_of_finalTranscript_eq
    (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (G : Space d → Ω' → ℝ) (tape : ℕ → Ω) (tape' : ℕ → Ω') (seed : S)
    (hfinal : A.finalTranscript F tape seed = A.finalTranscript G tape' seed)
    (t : ℕ) (ht : t ≤ N) :
    A.runPrefix F tape seed t = A.runPrefix G tape' seed t := by
  funext i
  by_cases hi : i.val < t
  · calc
      A.runPrefix F tape seed t i = A.runPrefix F tape seed N i :=
        (runPrefix_coordinate_stable A F tape seed t N ht i hi).symm
      _ = A.runPrefix G tape' seed N i := congrFun hfinal i
      _ = A.runPrefix G tape' seed t i :=
        runPrefix_coordinate_stable A G tape' seed t N ht i hi
  · rw [runPrefix_future_zero A F tape seed t i (by omega),
      runPrefix_future_zero A G tape' seed t i (by omega)]

/-- Equal replies along one actual adaptive execution force the other execution
to follow exactly the same path. No restriction on query spans is used. -/
theorem runPrefix_eq_of_along_execution_reply_eq
    (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (G : Space d → Ω' → ℝ) (tape : ℕ → Ω) (tape' : ℕ → Ω') (seed : S)
    (hreplies : ∀ i : Fin N,
      scalarReply F tape (A.executedAction F tape seed i) =
        scalarReply G tape' (A.executedAction F tape seed i)) (t : ℕ) :
    A.runPrefix F tape seed t = A.runPrefix G tape' seed t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [runPrefix, runPrefix]
    split_ifs with ht
    · rw [← ih]
      apply congrArg (Function.update (A.runPrefix F tape seed t) ⟨t, ht⟩)
      exact hreplies ⟨t, ht⟩
    · exact ih

/-- The value written at the paid slot is precisely its scalar reply. -/
theorem runPrefix_succ_self
    (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (i : Fin N) :
    A.runPrefix F tape seed (i.val + 1) i =
      scalarReply F tape (A.executedAction F tape seed i) := by
  simp [runPrefix, i.isLt, executedAction]

/-- Exact fibers of the complete adaptive transcript are constraints on replies
along that same transcript. -/
theorem finalTranscript_eq_iff_along_execution_reply_eq
    (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (G : Space d → Ω' → ℝ) (tape : ℕ → Ω) (tape' : ℕ → Ω') (seed : S) :
    A.finalTranscript F tape seed = A.finalTranscript G tape' seed ↔
      ∀ i : Fin N, scalarReply F tape (A.executedAction F tape seed i) =
        scalarReply G tape' (A.executedAction F tape seed i) := by
  constructor
  · intro hfinal i
    have hp := runPrefix_eq_of_finalTranscript_eq A F G tape tape' seed hfinal
      (i.val + 1) (by omega)
    have hpast := runPrefix_eq_of_finalTranscript_eq A F G tape tape' seed hfinal
      i.val (by omega)
    have hact : A.executedAction F tape seed i = A.executedAction G tape' seed i := by
      simp only [executedAction, hpast]
    have hvalue := congrFun hp i
    rw [runPrefix_succ_self, runPrefix_succ_self, ← hact] at hvalue
    exact hvalue
  · intro hreplies
    exact runPrefix_eq_of_along_execution_reply_eq A F G tape tape' seed hreplies N

/-- A later equal prefix determines every earlier prefix. -/
theorem runPrefix_eq_of_laterPrefix_eq
    (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (G : Space d → Ω' → ℝ) (tape : ℕ → Ω) (tape' : ℕ → Ω') (seed : S)
    (u : ℕ) (heq : A.runPrefix F tape seed u = A.runPrefix G tape' seed u)
    (t : ℕ) (ht : t ≤ u) :
    A.runPrefix F tape seed t = A.runPrefix G tape' seed t := by
  funext i
  by_cases hi : i.val < t
  · calc
      A.runPrefix F tape seed t i = A.runPrefix F tape seed u i :=
        (runPrefix_coordinate_stable A F tape seed t u ht i hi).symm
      _ = A.runPrefix G tape' seed u i := congrFun heq i
      _ = A.runPrefix G tape' seed t i :=
        runPrefix_coordinate_stable A G tape' seed t u ht i hi
  · rw [runPrefix_future_zero A F tape seed t i (by omega),
      runPrefix_future_zero A G tape' seed t i (by omega)]

/-- Reply constraints are needed only before the prefix in question. -/
theorem runPrefix_eq_of_along_reply_eq_before
    (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (G : Space d → Ω' → ℝ) (tape : ℕ → Ω) (tape' : ℕ → Ω') (seed : S)
    (t : ℕ)
    (hreplies : ∀ i : Fin N, i.val < t →
      scalarReply F tape (A.executedAction F tape seed i) =
        scalarReply G tape' (A.executedAction F tape seed i)) :
    A.runPrefix F tape seed t = A.runPrefix G tape' seed t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hprev := ih (fun i hi => hreplies i (by omega))
    rw [runPrefix, runPrefix]
    split_ifs with ht
    · rw [← hprev]
      apply congrArg (Function.update (A.runPrefix F tape seed t) ⟨t, ht⟩)
      exact hreplies ⟨t, ht⟩ (Nat.lt_succ_self t)
    · exact hprev

/-- Exact constraints for an arbitrary partial transcript, not only the output. -/
theorem runPrefix_eq_iff_along_reply_eq_before
    (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (G : Space d → Ω' → ℝ) (tape : ℕ → Ω) (tape' : ℕ → Ω') (seed : S)
    (t : ℕ) :
    A.runPrefix F tape seed t = A.runPrefix G tape' seed t ↔
      ∀ i : Fin N, i.val < t →
        scalarReply F tape (A.executedAction F tape seed i) =
          scalarReply G tape' (A.executedAction F tape seed i) := by
  constructor
  · intro hprefix i hi
    have hp := runPrefix_eq_of_laterPrefix_eq A F G tape tape' seed t hprefix
      (i.val + 1) (by omega)
    have hpast := runPrefix_eq_of_laterPrefix_eq A F G tape tape' seed t hprefix i.val (by omega)
    have hact : A.executedAction F tape seed i = A.executedAction G tape' seed i := by
      simp only [executedAction, hpast]
    have hvalue := congrFun hp i
    rw [runPrefix_succ_self, runPrefix_succ_self, ← hact] at hvalue
    exact hvalue
  · exact runPrefix_eq_of_along_reply_eq_before A F G tape tape' seed t

/-- The effective exact-linear measurement, after fixing the exogenous tape. -/
def effectiveVector (weight : Ω → ℝ) (tape : ℕ → Ω) : QueryAction d → Space d
  | none => 0
  | some (handle, point) => weight (tape handle) • point

def linearSample (weight : Ω → ℝ) (theta : Space d) : Space d → Ω → ℝ :=
  fun x omega => weight omega * inner ℝ theta x

theorem scalarReply_linear (weight : Ω → ℝ) (tape : ℕ → Ω)
    (theta : Space d) (action : QueryAction d) :
    scalarReply (linearSample weight theta) tape action =
      inner ℝ theta (effectiveVector weight tape action) := by
  cases action with
  | none => simp [scalarReply, effectiveVector]
  | some query =>
    rcases query with ⟨handle, point⟩
    simp [scalarReply, effectiveVector, linearSample, inner_smul_right]

/-- The actual finite policy produces precisely an affine linear-measurement
fiber, even when handles, stopping, and second points depend on earlier values. -/
theorem linear_transcript_fiber
    (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (theta theta' : Space d) :
    A.finalTranscript (linearSample weight theta) tape seed =
        A.finalTranscript (linearSample weight theta') tape seed ↔
      ∀ i : Fin N,
        inner ℝ theta (effectiveVector weight tape
          (A.executedAction (linearSample weight theta) tape seed i)) =
        inner ℝ theta' (effectiveVector weight tape
          (A.executedAction (linearSample weight theta) tape seed i)) := by
  rw [finalTranscript_eq_iff_along_execution_reply_eq]
  simp only [scalarReply_linear]

/-- Equivalent homogeneous form of the exact affine transcript fiber. -/
theorem linear_transcript_fiber_orthogonality
    (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (theta theta' : Space d) :
    A.finalTranscript (linearSample weight theta) tape seed =
        A.finalTranscript (linearSample weight theta') tape seed ↔
      ∀ i : Fin N,
        inner ℝ (theta' - theta) (effectiveVector weight tape
          (A.executedAction (linearSample weight theta) tape seed i)) = 0 := by
  rw [linear_transcript_fiber]
  constructor
  · intro h i
    rw [inner_sub_left]
    linarith [h i]
  · intro h i
    have hi := h i
    rw [inner_sub_left] at hi
    linarith

/-- The span describes information only; outputs and iterates are unrestricted. -/
def measurementSpan
    (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (theta : Space d) : Submodule ℝ (Space d) :=
  Submodule.span ℝ (Set.range (fun i : Fin N => effectiveVector weight tape
    (A.executedAction (linearSample weight theta) tape seed i)))

theorem orthogonal_span_iff (vectors : Fin N → Space d) (x : Space d) :
    x ∈ (Submodule.span ℝ (Set.range vectors)).orthogonal ↔
      ∀ i : Fin N, inner ℝ x (vectors i) = 0 := by
  rw [Submodule.mem_orthogonal']
  constructor
  · intro h i
    exact h (vectors i) (Submodule.subset_span (Set.mem_range_self i))
  · intro h u hu
    have hle : Submodule.span ℝ (Set.range vectors) ≤
        LinearMap.ker ((innerSL ℝ x).toLinearMap) := by
      apply Submodule.span_le.mpr
      rintro v ⟨i, rfl⟩
      change inner ℝ x (vectors i) = 0
      exact h i
    have hh := hle hu
    change inner ℝ x u = 0 at hh
    exact hh

/-- Exact orthogonal-complement description of every adaptive transcript fiber. -/
theorem linear_transcript_fiber_span
    (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (theta theta' : Space d) :
    A.finalTranscript (linearSample weight theta) tape seed =
        A.finalTranscript (linearSample weight theta') tape seed ↔
      theta' - theta ∈ (measurementSpan A weight tape seed theta).orthogonal := by
  rw [linear_transcript_fiber_orthogonality]
  exact (orthogonal_span_iff _ _).symm

/-- Equality of the projected component is exactly the homogeneous fiber condition. -/
theorem projection_eq_iff_sub_mem_orthogonal
    (V : Submodule ℝ (Space d)) (theta theta' : Space d) :
    V.orthogonalProjectionOnto theta = V.orthogonalProjectionOnto theta' ↔
      theta' - theta ∈ V.orthogonal := by
  constructor
  · intro h
    have hzero : V.orthogonalProjectionOnto (theta' - theta) = 0 := by
      rw [map_sub, h, sub_self]
    exact Submodule.orthogonalProjectionOnto_eq_zero_iff.mp hzero
  · intro h
    have hzero : V.orthogonalProjectionOnto (theta' - theta) = 0 :=
      Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr h
    rw [map_sub] at hzero
    exact (sub_eq_zero.mp hzero).symm

/-- The effective measurement span before a given paid slot. -/
def measurementSpanBefore
    (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (t : ℕ) (theta : Space d) : Submodule ℝ (Space d) :=
  Submodule.span ℝ (Set.range (fun i : {i : Fin N // i.val < t} => effectiveVector weight tape
    (A.executedAction (linearSample weight theta) tape seed i.val)))

theorem orthogonal_span_range_iff {J : Type*} (vectors : J → Space d) (x : Space d) :
    x ∈ (Submodule.span ℝ (Set.range vectors)).orthogonal ↔
      ∀ i : J, inner ℝ x (vectors i) = 0 := by
  rw [Submodule.mem_orthogonal']
  constructor
  · intro h i
    exact h (vectors i) (Submodule.subset_span (Set.mem_range_self i))
  · intro h u hu
    have hle : Submodule.span ℝ (Set.range vectors) ≤
        LinearMap.ker ((innerSL ℝ x).toLinearMap) := by
      apply Submodule.span_le.mpr
      rintro v ⟨i, rfl⟩
      change inner ℝ x (vectors i) = 0
      exact h i
    have hh := hle hu
    change inner ℝ x u = 0 at hh
    exact hh

/-- Exact affine-fiber condition at every intermediate adaptive history. -/
theorem linear_prefix_fiber_span
    (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (t : ℕ) (theta theta' : Space d) :
    A.runPrefix (linearSample weight theta) tape seed t =
        A.runPrefix (linearSample weight theta') tape seed t ↔
      theta' - theta ∈ (measurementSpanBefore A weight tape seed t theta).orthogonal := by
  rw [runPrefix_eq_iff_along_reply_eq_before]
  simp only [scalarReply_linear]
  rw [measurementSpanBefore, orthogonal_span_range_iff]
  constructor
  · intro h i
    rw [inner_sub_left]
    linarith [h i.val i.property]
  · intro h i hi
    have heq := h ⟨i, hi⟩
    rw [inner_sub_left] at heq
    linarith

theorem linear_prefix_fiber_projection
    (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (t : ℕ) (theta theta' : Space d) :
    A.runPrefix (linearSample weight theta) tape seed t =
        A.runPrefix (linearSample weight theta') tape seed t ↔
      (measurementSpanBefore A weight tape seed t theta).orthogonalProjectionOnto theta =
        (measurementSpanBefore A weight tape seed t theta).orthogonalProjectionOnto theta' := by
  rw [linear_prefix_fiber_span]
  exact (projection_eq_iff_sub_mem_orthogonal _ _ _).symm

/-- The observed projected center is the complete exact transcript constraint. -/
theorem linear_transcript_fiber_projection
    (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (theta theta' : Space d) :
    A.finalTranscript (linearSample weight theta) tape seed =
        A.finalTranscript (linearSample weight theta') tape seed ↔
      (measurementSpan A weight tape seed theta).orthogonalProjectionOnto theta =
        (measurementSpan A weight tape seed theta).orthogonalProjectionOnto theta' := by
  rw [linear_transcript_fiber_span]
  exact (projection_eq_iff_sub_mem_orthogonal _ _ _).symm

#print axioms runPrefix_eq_of_along_execution_reply_eq
#print axioms finalTranscript_eq_iff_along_execution_reply_eq
#print axioms scalarReply_linear
#print axioms linear_transcript_fiber
#print axioms linear_transcript_fiber_orthogonality
#print axioms orthogonal_span_iff
#print axioms linear_transcript_fiber_span
#print axioms projection_eq_iff_sub_mem_orthogonal
#print axioms linear_transcript_fiber_projection
#print axioms runPrefix_eq_iff_along_reply_eq_before
#print axioms linear_prefix_fiber_span
#print axioms linear_prefix_fiber_projection

end
end Task006.AdaptiveSphereTranscript
