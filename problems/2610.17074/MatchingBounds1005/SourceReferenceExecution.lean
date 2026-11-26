import MatchingBounds1005.SourceReferenceProtocol

/-! Exact execution of the genuine accessible source program. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace MatchingBounds1005.SourceReferenceReplay
open GaussianVector ReferenceState TensorChannelRows SequentialPosterior
open SourceReferenceProgram ShiftedSequential CensoredGaussianProcess
open GaussianNoiseStream FiniteGaussianSampler

variable {Rot Seed : Type} [MeasurableSpace Rot] [MeasurableSpace Seed] {d H N : ℕ}

theorem disclose_replay (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (n : ℕ)
    (h : History (Rot × Seed) (H * (d + d)) n) (z : Noise (jointDim d) H) :
    ReadoutCalendar.revealState P.b readoutUpdate (U (initialSeed n h).1)
      (VisibleReadouts.due P.disclosure (n + 1)) (withNoise z (replay P A U n h)) =
        withNoise z (before P A U n h) := by
  change ReadoutCalendar.revealState P.b (fun i => ⟨setReadout i, setReadout_measurable i⟩)
    (U (initialSeed n h).1) _ _ = _
  rw [revealState_eq, revealRows_withNoise]
  rfl

theorem query_replay (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (n : ℕ) (h : History (Rot × Seed) (H * (d + d)) n) (z : Noise (jointDim d) H) :
    (query P A (n + 1)).2.next
      (withNoise z (before P A U n h),
        U (initialSeed n h).1 (P.Q ((U (initialSeed n h).1).adjoint
          ((query P A (n + 1)).1.point (withNoise z (before P A U n h)))))) =
      withNoise z (replay P A U (n + 1)
        (h, response (protocol P A U hb hc hQ) 1 n ((protocol P A U hb hc hQ).visible n)
          (h, noiseAt H z n))) := by
  change finishQuery A (10 * P.τ * N) P.R P.η P.σ₃ P.σ₄ (correction P) n
    (withNoise z (before P A U n h),
      (U (initialSeed n h).1 (P.Q ((U (initialSeed n h).1).adjoint
        (confinedQuery A P.R n (withNoise z (before P A U n h))))),
        ReferenceTransition.transition 1
          (queryInput A P.τ P.a P.σ₃ P.σ₄ P.R n (withNoise z (before P A U n h)), noiseAt H z n))) = _
  rw [confinedQuery_withNoise, queryInput_withNoise, finishQuery_withNoise,
    transition_eq_reference P A U hb hc hQ]
  rfl

theorem initialSeed_runStream (f : (n : ℕ) → History (Rot × Seed) (H * (d + d)) n × Vec (jointDim d) → Fin (H * (d + d)) → ℝ)
    (ω : Rot × Seed) (noise : ℕ → Vec (jointDim d)) (n : ℕ) :
    initialSeed n (runStream f ω noise n) = ω := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

def referenceStream (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (ω : Rot × Seed) (z : Noise (jointDim d) H) :
    (n : ℕ) → History (Rot × Seed) (H * (d + d)) n :=
  runStream (fun n => response (protocol P A U hb hc hQ) 1 n ((protocol P A U hb hc hQ).visible n))
    ω (noiseAt H z)

theorem referenceStream_seed (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (ω : Rot × Seed) (z : Noise (jointDim d) H) (n : ℕ) :
    initialSeed n (referenceStream P A U hb hc hQ ω z n) = ω :=
  initialSeed_runStream _ _ _ _

theorem calendar_referenceStream (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (ω : Rot × Seed) (z : Noise (jointDim d) H) (j rounds : ℕ) :
    ReadoutCalendar.runCalendar P.b P.disclosure readoutUpdate (query P A) (candidate P A)
      P.Q (U ω.1) (j + 1) rounds
      (withNoise z (replay P A U j (referenceStream P A U hb hc hQ ω z j))) =
        withNoise z (replay P A U (j + rounds) (referenceStream P A U hb hc hQ ω z (j + rounds))) := by
  induction rounds generalizing j with
  | zero => rfl
  | succ rounds ih =>
      let h := referenceStream P A U hb hc hQ ω z j
      let s := before P A U j h
      have hseed : initialSeed j h = ω := referenceStream_seed P A U hb hc hQ ω z j
      have hdisclose : ReadoutCalendar.revealState P.b readoutUpdate (U ω.1)
          (VisibleReadouts.due P.disclosure (j + 1)) (withNoise z (replay P A U j h)) = withNoise z s := by
        rw [show (readoutUpdate (Seed := Seed) (d := d) (H := H) (N := N)) =
            (fun i => ⟨setReadout i, setReadout_measurable i⟩) from rfl,
          revealState_eq, revealRows_withNoise]
        unfold s before
        rw [hseed]
      have hnext : (query P A (j + 1)).2.next
          (withNoise z s, U ω.1 (P.Q ((U ω.1).adjoint ((query P A (j + 1)).1.point (withNoise z s))))) =
            withNoise z (replay P A U (j + 1) (referenceStream P A U hb hc hQ ω z (j + 1))) := by
        change finishQuery A (10 * P.τ * N) P.R P.η P.σ₃ P.σ₄ (correction P) j
          (withNoise z s, (U ω.1 (P.Q ((U ω.1).adjoint (confinedQuery A P.R j (withNoise z s)))),
            ReferenceTransition.transition 1
              (queryInput A P.τ P.a P.σ₃ P.σ₄ P.R j (withNoise z s), noiseAt H z j))) = _
        rw [confinedQuery_withNoise, queryInput_withNoise, finishQuery_withNoise]
        change withNoise z (finishQuery A (10 * P.τ * N) P.R P.η P.σ₃ P.σ₄ (correction P) j
          (s, (U ω.1 (P.Q ((U ω.1).adjoint (confinedQuery A P.R j s))),
            ReferenceTransition.transition 1 (queryInput A P.τ P.a P.σ₃ P.σ₄ P.R j (before P A U j h), noiseAt H z j)))) = _
        rw [transition_eq_reference P A U hb hc hQ]
        rw [replay_succ]
        change _ = withNoise z (finishQuery A (10 * P.τ * N) P.R P.η P.σ₃ P.σ₄ (correction P) j
          (s, (U (initialSeed j h).1 (P.Q ((U (initialSeed j h).1).adjoint (confinedQuery A P.R j s))),
            response (protocol P A U hb hc hQ) 1 j ((protocol P A U hb hc hQ).visible j) (h, noiseAt H z j))))
        rw [hseed]
      rw [ReadoutCalendar.runCalendar, hdisclose, hnext, ih]
      have he : j + 1 + rounds = j + (rounds + 1) := by omega
      rw [he]

theorem execute_referenceStream (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (ω : Rot × Seed) (z : Noise (jointDim d) H) :
    execute P A (U ω.1) (ω.2, z) =
      withNoise z (replay P A U H (referenceStream P A U hb hc hQ ω z H)) := by
  have he := calendar_referenceStream (H := H) P A U hb hc hQ ω z 0 H
  rw [Nat.zero_add H] at he
  exact he

end MatchingBounds1005.SourceReferenceReplay
