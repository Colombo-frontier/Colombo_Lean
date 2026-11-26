import MatchingBounds1005.SourceReferenceProgram
import MatchingBounds1005.ReferenceStateInvariant
import MatchingBounds1005.ReferenceTransitionLink

/-!
# Reconstructing the concrete reference state from raw Gaussian history

The comparison seed contains only the rotation and algorithm seed. A zero
placeholder fills the implementation's private-noise field; every query,
row and continuation is independent of that field. Real independent noise
is inserted only when compiling the separate Haar experiment.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace MatchingBounds1005.SourceReferenceReplay
open GaussianVector ReferenceState TensorChannelRows SequentialPosterior
open SourceReferenceProgram ShiftedSequential AccumulatedRows

variable {Rot Seed : Type} [MeasurableSpace Rot] [MeasurableSpace Seed] {d H N : ℕ}

def replay (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) :
    (n : ℕ) → History (Rot × Seed) (H * (d + d)) n → State Seed d H N
  | 0, h => setLinear (initial (h.2, zeroNoise (jointDim d) H), U h.1 P.c)
  | n + 1, h =>
      let V := U (initialSeed n h.1).1
      let s := revealRows P.b V (VisibleReadouts.due P.disclosure (n + 1)) (replay P A U n h.1)
      let x := confinedQuery A P.R n s
      finishQuery A (10 * P.τ * N) P.R P.η P.σ₃ P.σ₄ (correction P) n
        (s, (V (P.Q (V.adjoint x)), h.2))

def before (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (n : ℕ)
    (h : History (Rot × Seed) (H * (d + d)) n) : State Seed d H N :=
  revealRows P.b (U (initialSeed n h).1) (VisibleReadouts.due P.disclosure (n + 1))
    (replay P A U n h)

theorem replay_succ (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (n : ℕ)
    (h : History (Rot × Seed) (H * (d + d)) (n + 1)) :
    replay P A U (n + 1) h =
      finishQuery A (10 * P.τ * N) P.R P.η P.σ₃ P.σ₄ (correction P) n
        (before P A U n h.1,
          (U (initialSeed n h.1).1 (P.Q ((U (initialSeed n h.1).1).adjoint
            (confinedQuery A P.R n (before P A U n h.1)))), h.2)) := rfl

theorem replay_measurable (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (n : ℕ) : Measurable (replay (H := H) P A U n) := by
  induction n with
  | zero =>
      exact setLinear_measurable.comp
        ((initial_measurable.comp (measurable_snd.prodMk measurable_const)).prodMk
          (hc.comp measurable_fst))
  | succ n ih =>
      have hr : Measurable (fun h : History (Rot × Seed) (H * (d + d)) n => (initialSeed n h).1) :=
        measurable_fst.comp (initialSeed_measurable n)
      have hs : Measurable (before P A U n) :=
        (revealRows_joint_measurable P.b U hb _).comp (hr.prodMk ih)
      have hx := (confinedQuery_measurable (H := H) (N := N) A P.R n).comp hs
      have hphysical := hQ.comp (hr.prodMk hx)
      exact (finishQuery_measurable A (10 * P.τ * N) P.R P.η P.σ₃ P.σ₄
        (correction P) (correction_measurable P) n).comp
          ((hs.comp measurable_fst).prodMk
            ((hphysical.comp measurable_fst).prodMk measurable_snd))

theorem before_measurable (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (n : ℕ) : Measurable (before (H := H) P A U n) :=
  (revealRows_joint_measurable P.b U hb _).comp
    ((measurable_fst.comp (initialSeed_measurable n)).prodMk (replay_measurable P A U hb hc hQ n))

def current (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (n : ℕ)
    (h : History (Rot × Seed) (H * (d + d)) n) : Fin (d + d) → Vec (jointDim d) :=
  jointRows P.σ₃ P.σ₄ (confinedQuery A P.R n (before P A U n h))

theorem queryRows_before (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (n : ℕ)
    (h : History (Rot × Seed) (H * (d + d)) n) :
    queryRows A P.σ₃ P.σ₄ P.R n (before P A U n h) = accumulated (current P A U) n h := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext i
      change (if (slot i).val = n + 1 then current P A U (n + 1) h (coordinate i)
        else queryRows A P.σ₃ P.σ₄ P.R n (before P A U n h.1) i) = _
      rw [ih h.1]
      rfl

theorem oldRows_before (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (n : ℕ)
    (h : History (Rot × Seed) (H * (d + d)) n) :
    (before P A U n h).2.2.2.1 = ReferenceTransitionLink.oldRows (accumulated (current P A U)) n h := by
  cases n with
  | zero => rfl
  | succ n => exact queryRows_before P A U n h.1

theorem oldAnswers_before (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (n : ℕ)
    (h : History (Rot × Seed) (H * (d + d)) n) :
    (before P A U n h).2.2.2.2 = ReferenceTransitionLink.oldAnswers n h := by
  cases n <;> rfl

theorem replay_readouts (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (hτ : ∀ i, 0 < P.disclosure i) (n : ℕ)
    (h : History (Rot × Seed) (H * (d + d)) n) :
    (replay P A U n h).2.1.1 =
      VisibleReadouts.visibleAt P.disclosure P.b (U (initialSeed n h).1) n := by
  induction n with
  | zero => exact (VisibleReadouts.visibleAt_zero P.disclosure hτ P.b (U h.1)).symm
  | succ n ih =>
      change VisibleReadouts.reveal P.b (U (initialSeed n h.1).1)
        (VisibleReadouts.due P.disclosure (n + 1)) (replay P A U n h.1).2.1.1 = _
      rw [ih h.1, VisibleReadouts.reveal_due]
      rfl

theorem before_readouts (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (hτ : ∀ i, 0 < P.disclosure i) (n : ℕ)
    (h : History (Rot × Seed) (H * (d + d)) n) :
    (before P A U n h).2.1.1 =
      VisibleReadouts.visibleAt P.disclosure P.b (U (initialSeed n h).1) (n + 1) := by
  change VisibleReadouts.reveal P.b (U (initialSeed n h).1)
    (VisibleReadouts.due P.disclosure (n + 1)) (replay P A U n h).2.1.1 = _
  rw [replay_readouts P A U hτ, VisibleReadouts.reveal_due]

theorem replay_linear (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (n : ℕ)
    (h : History (Rot × Seed) (H * (d + d)) n) :
    (replay P A U n h).2.1.2 = U (initialSeed n h).1 P.c := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih h.1

theorem replay_private (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (n : ℕ)
    (h : History (Rot × Seed) (H * (d + d)) n) :
    (replay P A U n h).1 = ((initialSeed n h).2, zeroNoise (jointDim d) H) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih h.1

end MatchingBounds1005.SourceReferenceReplay
