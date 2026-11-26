import MatchingBounds1005.SourceStaticResponse
import MatchingBounds1005.SourceReferenceLaw
import MatchingBounds1005.StaticGaussianSampler
import MatchingBounds1005.OracleFirstExit

/-! Exact true-side recovery of the physical oracle transcript. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace MatchingBounds1005.SourceReferenceReplay
open GaussianVector ReferenceState TensorChannelRows SequentialPosterior
open SourceReferenceProgram ShiftedSequential GaussianFitter AccumulatedRows

variable {Rot Seed : Type} [MeasurableSpace Rot] [MeasurableSpace Seed] {d H N : ℕ}

def directReply (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Vec d →L[ℝ] Vec d) (z : Vec (jointDim d))
    (n : ℕ) (seed : Seed) (h : Fin n → Model.Response d) : Model.Response d :=
  directResponse P U z n (A.query n seed h)

def staticHistory (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (ω : Rot × Seed) (z : Vec (jointDim d))
    (n : ℕ) : History (Rot × Seed) (H * (d + d)) n :=
  StaticGaussianSampler.run (accumulated (current P A U)) ω (fullSignal P U ω.1 + z) n

theorem staticHistory_seed (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (ω : Rot × Seed) (z : Vec (jointDim d)) (n : ℕ) :
    initialSeed n (staticHistory (H := H) P A U ω z n) = ω :=
  StaticGaussianSampler.initialSeed_run _ _ _ _

theorem staticHistory_succ (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (ω : Rot × Seed) (z : Vec (jointDim d)) (n : ℕ) :
    staticHistory (H := H) P A U ω z (n + 1) =
      (staticHistory (H := H) P A U ω z n,
        rowResponse (accumulated (current P A U) n (staticHistory (H := H) P A U ω z n)) (fullSignal P U ω.1 + z)) := rfl

theorem update_restrict {α : Type} (old : ℕ → α) (n : ℕ) (y : α) :
    (fun i : Fin (n + 1) => Function.update old n y i.val) = Fin.snoc (fun i : Fin n => old i.val) y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.val_last, Function.update_self, Fin.snoc_last]
  · rw [Fin.snoc_castSucc]
    exact Function.update_of_ne (Nat.ne_of_lt j.isLt) _ _

theorem replay_static_update (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (hτ : ∀ i, 0 < P.disclosure i)
    (hr : 1 ≤ P.r) (hσ₃ : P.σ₃ ≠ 0) (hσ₄ : P.σ₄ ≠ 0)
    (ω : Rot × Seed) (z : Vec (jointDim d)) (n : ℕ) (hn : n < H) :
    (replay P A U (n + 1) (staticHistory (H := H) P A U ω z (n + 1))).2.2.1 =
      Function.update (replay P A U n (staticHistory (H := H) P A U ω z n)).2.2.1 n
        (directResponse P (U ω.1) z n (queryPoint A n (before P A U n (staticHistory (H := H) P A U ω z n)))) := by
  have ha := assembled_static P A U hτ hr hσ₃ hσ₄ n hn (staticHistory (H := H) P A U ω z n) z
  rw [staticHistory_seed] at ha
  rw [staticHistory_succ, replay_succ]
  change Function.update _ n _ = Function.update _ n _
  rw [staticHistory_seed, ha]
  rfl

theorem static_replay_transcript (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (hτ : ∀ i, 0 < P.disclosure i)
    (hr : 1 ≤ P.r) (hσ₃ : P.σ₃ ≠ 0) (hσ₄ : P.σ₄ ≠ 0)
    (ω : Rot × Seed) (z : Vec (jointDim d)) (n : ℕ) (hn : n ≤ H) :
    (fun i : Fin n => (replay P A U n (staticHistory (H := H) P A U ω z n)).2.2.1 i.val) =
      Model.replyTranscript (directReply P A (U ω.1) z) ω.2 n := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
      have hprev := ih (Nat.le_of_succ_le hn)
      have hseed : (before P A U n (staticHistory (H := H) P A U ω z n)).1.1 = ω.2 := by
        change (replay P A U n (staticHistory (H := H) P A U ω z n)).1.1 = _
        rw [replay_private, staticHistory_seed]
      have hquery : queryPoint A n (before P A U n (staticHistory (H := H) P A U ω z n)) =
          A.query n ω.2 (Model.replyTranscript (directReply P A (U ω.1) z) ω.2 n) := by
        unfold queryPoint
        rw [hseed]
        change A.query n ω.2 (fun i => (replay P A U n (staticHistory (H := H) P A U ω z n)).2.2.1 i.val) = _
        rw [hprev]
      simp only [replay_static_update P A U hτ hr hσ₃ hσ₄ ω z n (Nat.lt_of_succ_le hn)]
      rw [update_restrict, hprev, hquery]
      rfl

theorem static_trace_exact (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (hτ : ∀ i, 0 < P.disclosure i)
    (hr : 1 ≤ P.r) (hσ₃ : P.σ₃ ≠ 0) (hσ₄ : P.σ₄ ≠ 0)
    (ω : Rot × Seed) (z : Vec (jointDim d)) :
    trace (H := H) P A U H (staticHistory (H := H) P A U ω z H) =
      (ω, Model.replyTranscript (directReply P A (U ω.1) z) ω.2 H) := by
  unfold trace
  rw [staticHistory_seed, static_replay_transcript P A U hτ hr hσ₃ hσ₄ ω z H le_rfl]

end MatchingBounds1005.SourceReferenceReplay

