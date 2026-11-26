import MatchingBounds1005.SourceReferenceExecution
import MatchingBounds1005.SourceCalendarIndices
import MatchingBounds1005.AccessibleReferenceTrace

/-! The actual analyst query slots equal the reference experiment's physical queries. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace MatchingBounds1005.SourceReferenceReplay
open GaussianVector ReferenceState TensorChannelRows SequentialPosterior
open SourceReferenceProgram ShiftedSequential CensoredGaussianProcess
open GaussianNoiseStream FiniteGaussianSampler AccessibleReferenceCompiler

variable {Rot Seed : Type} [MeasurableSpace Rot] [MeasurableSpace Seed] {d H N : ℕ}

def calendarTrace (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (ω : Rot × Seed) (z : Noise (jointDim d) H) (j rounds : ℕ) :
    Fin (ReadoutCalendar.kinds P.disclosure (j + 1) rounds).length → Vec d :=
  inverseTrace _
    (ReadoutCalendar.machine P.b P.disclosure readoutUpdate (query P A) (candidate P A) (j + 1) rounds)
    P.Q (U ω.1) (withNoise z (replay P A U j (referenceStream P A U hb hc hQ ω z j)))

theorem calendarTrace_head (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (ω : Rot × Seed) (z : Noise (jointDim d) H) (j rounds : ℕ) :
    calendarTrace P A U hb hc hQ ω z j (rounds + 1)
      ⟨(VisibleReadouts.due P.disclosure (j + 1)).length,
        by simp [ReadoutCalendar.kinds, ReadoutCalendar.prependKinds]⟩ =
      (U ω.1).adjoint (confinedQuery A P.R j (before P A U j (referenceStream P A U hb hc hQ ω z j))) := by
  change inverseTrace (ReadoutCalendar.prependKinds _ _) (ReadoutCalendar.prependMachine _ _ _ _ _)
    _ _ _ ⟨(VisibleReadouts.due P.disclosure (j + 1)).length + (0 : Fin (
      (ReadoutCalendar.kinds P.disclosure (j + 2) rounds).length + 1)).val, _⟩ = _
  rw [ReadoutCalendar.inverseTrace_prepend]
  change (U ω.1).adjoint ((query P A (j + 1)).1.point
    (ReadoutCalendar.revealState P.b readoutUpdate (U ω.1) _
      (withNoise z (replay P A U j (referenceStream P A U hb hc hQ ω z j))))) = _
  have hd := disclose_replay P A U j (referenceStream P A U hb hc hQ ω z j) z
  rw [referenceStream_seed] at hd
  rw [hd]
  rfl

theorem calendarTrace_tail (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (ω : Rot × Seed) (z : Noise (jointDim d) H) (j rounds : ℕ)
    (i : Fin (ReadoutCalendar.kinds P.disclosure (j + 2) rounds).length) :
    calendarTrace P A U hb hc hQ ω z j (rounds + 1)
      ⟨(VisibleReadouts.due P.disclosure (j + 1)).length + (i.val + 1),
        by simp only [ReadoutCalendar.kinds, ReadoutCalendar.prependKinds,
          List.length_append, List.length_map, List.length_cons]
           have hi := i.isLt
           have he : (ReadoutCalendar.kinds P.disclosure (j + 1 + 1) rounds).length =
               (ReadoutCalendar.kinds P.disclosure (j + 2) rounds).length :=
             congrArg (fun n => (ReadoutCalendar.kinds P.disclosure n rounds).length) (by omega)
           omega⟩ =
        calendarTrace P A U hb hc hQ ω z (j + 1) rounds i := by
  change inverseTrace (ReadoutCalendar.prependKinds _ _) (ReadoutCalendar.prependMachine _ _ _ _ _)
    _ _ _ ⟨(VisibleReadouts.due P.disclosure (j + 1)).length + i.succ.val, _⟩ = _
  rw [ReadoutCalendar.inverseTrace_prepend]
  change inverseTrace _ _ P.Q (U ω.1)
    ((query P A (j + 1)).2.next
      (ReadoutCalendar.revealState P.b readoutUpdate (U ω.1) _
        (withNoise z (replay P A U j (referenceStream P A U hb hc hQ ω z j))),
       U ω.1 (P.Q ((U ω.1).adjoint ((query P A (j + 1)).1.point
         (ReadoutCalendar.revealState P.b readoutUpdate (U ω.1) _
           (withNoise z (replay P A U j (referenceStream P A U hb hc hQ ω z j))))))))) i = _
  have hd := disclose_replay P A U j (referenceStream P A U hb hc hQ ω z j) z
  rw [referenceStream_seed] at hd
  rw [hd]
  have hnext := query_replay P A U hb hc hQ j (referenceStream P A U hb hc hQ ω z j) z
  rw [referenceStream_seed] at hnext
  rw [hnext]
  rfl

theorem calendarTrace_queryIndex (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (ω : Rot × Seed) (z : Noise (jointDim d) H) (j rounds k : ℕ) (hk : k < rounds) :
    calendarTrace P A U hb hc hQ ω z j rounds
      ⟨ReadoutCalendar.queryIndex P.disclosure (j + 1) k,
        ReadoutCalendar.queryIndex_lt_length _ _ _ _ hk⟩ =
      (U ω.1).adjoint (confinedQuery A P.R (j + k)
        (before P A U (j + k) (referenceStream P A U hb hc hQ ω z (j + k)))) := by
  induction k generalizing j rounds with
  | zero =>
      cases rounds with
      | zero => omega
      | succ rounds => exact calendarTrace_head P A U hb hc hQ ω z j rounds
  | succ k ih =>
      cases rounds with
      | zero => omega
      | succ rounds =>
          have hk' : k < rounds := by omega
          have ht := calendarTrace_tail P A U hb hc hQ ω z j rounds
            ⟨ReadoutCalendar.queryIndex P.disclosure (j + 2) k,
              ReadoutCalendar.queryIndex_lt_length _ _ _ _ hk'⟩
          have he : ReadoutCalendar.queryIndex P.disclosure (j + 1) (k + 1) =
              (VisibleReadouts.due P.disclosure (j + 1)).length +
                (ReadoutCalendar.queryIndex P.disclosure (j + 2) k + 1) := by
            rw [ReadoutCalendar.queryIndex]
            rw [show j + 1 + 1 = j + 2 by omega]
            omega
          simp only [he] at *
          rw [ht, ih (j + 1) rounds hk']
          have he' : j + 1 + k = j + (k + 1) := by omega
          rw [he']

theorem calendarTrace_candidateIndex (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (ω : Rot × Seed) (z : Noise (jointDim d) H) (j rounds : ℕ) :
    calendarTrace P A U hb hc hQ ω z j rounds
      ⟨ReadoutCalendar.candidateIndex P.disclosure (j + 1) rounds,
        ReadoutCalendar.candidateIndex_lt_length _ _ _⟩ =
      (U ω.1).adjoint (candidatePoint P A (j + rounds + 1)
        (replay P A U (j + rounds) (referenceStream P A U hb hc hQ ω z (j + rounds)))) := by
  induction rounds generalizing j with
  | zero => rfl
  | succ rounds ih =>
      have ht := calendarTrace_tail P A U hb hc hQ ω z j rounds
        ⟨ReadoutCalendar.candidateIndex P.disclosure (j + 2) rounds,
          ReadoutCalendar.candidateIndex_lt_length _ _ _⟩
      have he : ReadoutCalendar.candidateIndex P.disclosure (j + 1) (rounds + 1) =
          (VisibleReadouts.due P.disclosure (j + 1)).length +
            (ReadoutCalendar.candidateIndex P.disclosure (j + 2) rounds + 1) := by
        rw [ReadoutCalendar.candidateIndex]
        rw [show j + 1 + 1 = j + 2 by omega]
        omega
      simp only [he] at *
      rw [ht, ih (j + 1)]
      have he' : j + 1 + rounds = j + (rounds + 1) := by omega
      rw [he']

theorem planTrace_queryIndex (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (ω : Rot × Seed) (z : Noise (jointDim d) H) (j : ℕ) (hj : j < H) :
    ScheduledHaar.roundQueryTrace (Vec d) (commands P H).length
      (((plan P A).compile (commands P H)).run (commands P H).length P.Q (U ω.1) (ω.2, z))
      ⟨SourceReferenceProgram.queryIndex P j, SourceReferenceProgram.queryIndex_lt_length P H j hj⟩ =
      (U ω.1).adjoint (confinedQuery A P.R j
        (before P A U j (referenceStream P A U hb hc hQ ω z j))) := by
  rw [plan, compile_inverseTrace]
  change Fin.cons (α := fun _ : Fin ((ReadoutCalendar.kinds P.disclosure 1 H).length + 1) => Vec d)
    0 (calendarTrace P A U hb hc hQ ω z 0 H)
    ⟨1 + ReadoutCalendar.queryIndex P.disclosure 1 j, _⟩ = _
  have he : (⟨1 + ReadoutCalendar.queryIndex P.disclosure 1 j,
      by have hi := ReadoutCalendar.queryIndex_lt_length P.disclosure 1 H j hj; omega⟩ :
      Fin ((ReadoutCalendar.kinds P.disclosure 1 H).length + 1)) =
      (⟨ReadoutCalendar.queryIndex P.disclosure 1 j,
        ReadoutCalendar.queryIndex_lt_length _ _ _ _ hj⟩ : Fin (ReadoutCalendar.kinds P.disclosure 1 H).length).succ := by
    apply Fin.ext
    simp only [Fin.val_succ]
    omega
  rw [he, Fin.cons_succ]
  have hq := calendarTrace_queryIndex P A U hb hc hQ ω z 0 H j hj
  rw [Nat.zero_add j] at hq
  exact hq

theorem planTrace_candidateIndex (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (ω : Rot × Seed) (z : Noise (jointDim d) H) :
    ScheduledHaar.roundQueryTrace (Vec d) (commands P H).length
      (((plan P A).compile (commands P H)).run (commands P H).length P.Q (U ω.1) (ω.2, z))
      ⟨SourceReferenceProgram.candidateIndex P H, SourceReferenceProgram.candidateIndex_lt_length P H⟩ =
      (U ω.1).adjoint (candidatePoint P A (H + 1)
        (replay P A U H (referenceStream P A U hb hc hQ ω z H))) := by
  rw [plan, compile_inverseTrace]
  change Fin.cons (α := fun _ : Fin ((ReadoutCalendar.kinds P.disclosure 1 H).length + 1) => Vec d)
    0 (calendarTrace P A U hb hc hQ ω z 0 H)
    ⟨1 + ReadoutCalendar.candidateIndex P.disclosure 1 H, _⟩ = _
  have he : (⟨1 + ReadoutCalendar.candidateIndex P.disclosure 1 H,
      by have hi := ReadoutCalendar.candidateIndex_lt_length P.disclosure 1 H; omega⟩ :
      Fin ((ReadoutCalendar.kinds P.disclosure 1 H).length + 1)) =
      (⟨ReadoutCalendar.candidateIndex P.disclosure 1 H,
        ReadoutCalendar.candidateIndex_lt_length _ _ _⟩ : Fin (ReadoutCalendar.kinds P.disclosure 1 H).length).succ := by
    apply Fin.ext
    simp only [Fin.val_succ]
    omega
  rw [he, Fin.cons_succ]
  have hq := calendarTrace_candidateIndex P A U hb hc hQ ω z 0 H
  rw [Nat.zero_add H] at hq
  exact hq

end MatchingBounds1005.SourceReferenceReplay
