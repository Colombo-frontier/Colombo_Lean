import MatchingBounds1005.SourceReferenceExecution

/-!
# Actual accessible-reference transcript law

The source program uses private Gaussian noise independent of the rotation.
After forgetting that private noise, its oracle transcript has exactly the
censored Gaussian reference law, which is the measure used in the KL proof.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace MatchingBounds1005.SourceReferenceReplay
open GaussianVector ReferenceState TensorChannelRows SequentialPosterior
open SourceReferenceProgram ShiftedSequential CensoredGaussianProcess
open GaussianNoiseStream FiniteGaussianSampler CensoredReferenceSampler

variable {Rot Seed : Type} [MeasurableSpace Rot] [MeasurableSpace Seed] {d H N : ℕ}

def trace (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (n : ℕ)
    (h : History (Rot × Seed) (H * (d + d)) n) : (Rot × Seed) × (Fin n → Model.Response d) :=
  (initialSeed n h, fun i => (replay P A U n h).2.2.1 i.val)

theorem trace_measurable (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (n : ℕ) : Measurable (trace (H := H) P A U n) := by
  apply (initialSeed_measurable n).prodMk
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply i.val).comp (replay_measurable P A U hb hc hQ n).snd.snd.fst

def programTrace (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (p : Rot × (Seed × Noise (jointDim d) H)) : (Rot × Seed) × (Fin H → Model.Response d) :=
  ((p.1, p.2.1), fun i => (execute P A (U p.1) p.2).2.2.1 i.val)

theorem referenceStream_sample (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (p : Rot × (Seed × Noise (jointDim d) H)) :
    referenceStream P A U hb hc hQ (p.1, p.2.1) p.2.2 H =
      privateSample (protocol (H := H) P A U hb hc hQ) 1 H p :=
  runStream_noiseAt _ _ _ _

theorem programTrace_eq (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (p : Rot × (Seed × Noise (jointDim d) H)) :
    programTrace P A U p = trace (H := H) P A U H (privateSample (protocol (H := H) P A U hb hc hQ) 1 H p) := by
  rw [← referenceStream_sample P A U hb hc hQ p]
  unfold programTrace trace
  rw [referenceStream_seed, execute_referenceStream P A U hb hc hQ (p.1, p.2.1) p.2.2]
  rfl

theorem programTrace_measurable (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2)))) :
    Measurable (programTrace (H := H) P A U) := by
  have heq : programTrace (H := H) P A U =
      fun p => trace (H := H) P A U H (privateSample (protocol (H := H) P A U hb hc hQ) 1 H p) :=
    funext (programTrace_eq P A U hb hc hQ)
  rw [heq]
  exact (trace_measurable P A U hb hc hQ H).comp (privateSample_measurable _ _ _)

/-- Equality of actual measures, with the complete Gaussian seed independent
of the rotation and absent from the comparison transcript's initial seed. -/
theorem programTrace_law (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (νR : Measure Rot) (νS : Measure Seed) [IsProbabilityMeasure νR] [IsProbabilityMeasure νS] :
    (νR.prod (νS.prod (noiseLaw (jointDim d) H))).map (programTrace P A U) =
      (referenceLaw (protocol (H := H) P A U hb hc hQ) 1 (νR.prod νS) H).map (trace (H := H) P A U H) := by
  rw [← privateSample_law (protocol (H := H) P A U hb hc hQ) 1 νR νS H,
    Measure.map_map (trace_measurable P A U hb hc hQ H) (privateSample_measurable _ _ _)]
  congr 1
  funext p
  exact programTrace_eq P A U hb hc hQ p

end MatchingBounds1005.SourceReferenceReplay

