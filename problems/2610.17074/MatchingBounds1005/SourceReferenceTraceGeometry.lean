import MatchingBounds1005.SourceReferenceQueryTrace
import MatchingBounds1005.SourceReferenceLaw
import MatchingBounds1005.SourceReferencePrefix
import MatchingBounds1005.AlgorithmQueryTrace

/-! The source analyst trace compresses to the actual finite algorithm query trace. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace MatchingBounds1005.SourceReferenceReplay
open GaussianVector ReferenceState TensorChannelRows SequentialPosterior
open SourceReferenceProgram ShiftedSequential CensoredGaussianProcess
open GaussianNoiseStream FiniteGaussianSampler AccessibleReferenceCompiler

variable {Rot Seed : Type} [MeasurableSpace Rot] [MeasurableSpace Seed] {d H N : ℕ}

theorem stream_query_final (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (ω : Rot × Seed) (z : Noise (jointDim d) H) (j : Fin H) :
    confinedQuery A P.R j.val (before P A U j.val (referenceStream P A U hb hc hQ ω z j.val)) =
      Model.queryTrace P.R A H (ω.2, (programTrace P A U (ω.1, (ω.2, z))).2) j.castSucc := by
  rw [Model.queryTrace_query]
  have hs : (before P A U j.val (referenceStream P A U hb hc hQ ω z j.val)).1.1 = ω.2 := by
    change (replay P A U j.val (referenceStream P A U hb hc hQ ω z j.val)).1.1 = _
    rw [replay_private, referenceStream_seed]
  unfold confinedQuery queryPoint programTrace
  dsimp only
  rw [hs, execute_referenceStream P A U hb hc hQ ω z]
  apply congrArg (radial P.R)
  apply congrArg (A.query j.val ω.2)
  funext i
  exact (replay_stream_prefix P A U _ ω (noiseAt H z) H j.val (Nat.le_of_lt j.isLt) i.val i.isLt).symm

theorem stream_candidate_final (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (ω : Rot × Seed) (z : Noise (jointDim d) H) :
    candidatePoint P A (H + 1) (replay P A U H (referenceStream P A U hb hc hQ ω z H)) =
      Model.queryTrace P.R A H (ω.2, (programTrace P A U (ω.1, (ω.2, z))).2) (Fin.last H) := by
  rw [Model.queryTrace_output]
  unfold candidatePoint programTrace
  dsimp only
  rw [execute_referenceStream P A U hb hc hQ ω z, replay_private, referenceStream_seed]
  rw [Nat.add_sub_cancel H 1]
  rfl

/-- Equality of the complete compressed inverse-query trace, including the
candidate chosen after all H responses. The algorithm history is recovered
from its actual source execution, with all private Gaussian noise forgotten. -/
theorem planTrace_compressed (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (ω : Rot × Seed) (z : Noise (jointDim d) H) :
    (fun i => ScheduledHaar.roundQueryTrace (Vec d) (commands P H).length
      (((plan P A).compile (commands P H)).run (commands P H).length P.Q (U ω.1) (ω.2, z))
      (observationIndex P H i)) =
      fun i => (U ω.1).adjoint (Model.queryTrace P.R A H
        (ω.2, (programTrace P A U (ω.1, (ω.2, z))).2) i) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have he : observationIndex P H (Fin.last H) =
        ⟨candidateIndex P H, candidateIndex_lt_length P H⟩ := by
      apply Fin.ext
      exact observationIndex_candidate P H
    rw [he, planTrace_candidateIndex P A U hb hc hQ ω z,
      stream_candidate_final P A U hb hc hQ ω z]
  · have he : observationIndex P H j.castSucc =
        ⟨queryIndex P j.val, queryIndex_lt_length P H j.val j.isLt⟩ := by
      apply Fin.ext
      exact observationIndex_query P H j
    rw [he, planTrace_queryIndex P A U hb hc hQ ω z j.val j.isLt,
      stream_query_final P A U hb hc hQ ω z j]

end MatchingBounds1005.SourceReferenceReplay
