import MatchingBounds1005.SourceReferenceReplay
import MatchingBounds1005.HistoryPath

/-! The retained oracle array preserves every earlier policy history exactly. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace MatchingBounds1005.SourceReferenceReplay
open GaussianVector ReferenceState TensorChannelRows SequentialPosterior
open SourceReferenceProgram ShiftedSequential HistoryPath GaussianNoiseStream

variable {Rot Seed : Type} [MeasurableSpace Rot] [MeasurableSpace Seed] {d H N : ℕ}

theorem replay_history_previous (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (n : ℕ)
    (h : History (Rot × Seed) (H * (d + d)) (n + 1)) (i : ℕ) (hi : i < n) :
    (replay P A U (n + 1) h).2.2.1 i = (replay P A U n h.1).2.2.1 i :=
  Function.update_of_ne (Nat.ne_of_lt hi) _ _

theorem initialSeed_path (ω : Rot × Seed) (answers : ℕ → Fin (H * (d + d)) → ℝ) (n : ℕ) :
    initialSeed n (path ω answers n) = ω := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem replay_path_prefix (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (ω : Rot × Seed) (answers : ℕ → Fin (H * (d + d)) → ℝ)
    (n m : ℕ) (hmn : m ≤ n) (i : ℕ) (hi : i < m) :
    (replay P A U n (path ω answers n)).2.2.1 i =
      (replay P A U m (path ω answers m)).2.2.1 i := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hm : m = n + 1
      · subst m; rfl
      · have hmn' : m ≤ n := by omega
        rw [replay_history_previous P A U n _ i (hi.trans_le hmn')]
        exact ih hmn'

theorem queryPoint_path_final (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (ω : Rot × Seed) (answers : ℕ → Fin (H * (d + d)) → ℝ)
    (T j : ℕ) (hj : j ≤ T) :
    queryPoint A j (before P A U j (path ω answers j)) =
      A.query j ω.2 (fun i => (replay P A U T (path ω answers T)).2.2.1 i.val) := by
  have hs : (before P A U j (path ω answers j)).1.1 = ω.2 := by
    change (replay P A U j (path ω answers j)).1.1 = _
    rw [replay_private, initialSeed_path]
  unfold queryPoint
  rw [hs]
  apply congrArg (A.query j ω.2)
  funext i
  exact (replay_path_prefix P A U ω answers T j hj i.val i.isLt).symm

theorem replay_stream_prefix (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (f : (n : ℕ) → History (Rot × Seed) (H * (d + d)) n × Vec (jointDim d) → Fin (H * (d + d)) → ℝ)
    (ω : Rot × Seed) (noise : ℕ → Vec (jointDim d))
    (n m : ℕ) (hmn : m ≤ n) (i : ℕ) (hi : i < m) :
    (replay P A U n (runStream f ω noise n)).2.2.1 i =
      (replay P A U m (runStream f ω noise m)).2.2.1 i := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hm : m = n + 1
      · subst m; rfl
      · have hmn' : m ≤ n := by omega
        rw [replay_history_previous P A U n _ i (hi.trans_le hmn')]
        exact ih hmn'

end MatchingBounds1005.SourceReferenceReplay
