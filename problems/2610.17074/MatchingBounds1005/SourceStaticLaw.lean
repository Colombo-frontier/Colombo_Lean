import MatchingBounds1005.SourceStaticTrace

/-! Equality between the actual fixed Gaussian tensor experiment and true transcript law. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace MatchingBounds1005.SourceReferenceReplay
open GaussianVector ReferenceState TensorChannelRows SequentialPosterior
open SourceReferenceProgram ShiftedSequential CensoredGaussianProcess

variable {Rot Seed : Type} [MeasurableSpace Rot] [MeasurableSpace Seed] {d H N : ℕ}

def directTrace (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (H : ℕ)
    (p : (Rot × Seed) × Vec (jointDim d)) : (Rot × Seed) × (Fin H → Model.Response d) :=
  (p.1, Model.replyTranscript (directReply P A (U p.1.1) p.2) p.1.2 H)

theorem directTrace_measurable (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (hτ : ∀ i, 0 < P.disclosure i) (hr : 1 ≤ P.r) (hσ₃ : P.σ₃ ≠ 0) (hσ₄ : P.σ₄ ≠ 0) :
    Measurable (directTrace P A U H) := by
  have heq : directTrace P A U H =
      fun p : (Rot × Seed) × Vec (jointDim d) => trace (H := H) P A U H (staticHistory P A U p.1 p.2 H) := by
    funext p
    exact (static_trace_exact P A U hτ hr hσ₃ hσ₄ p.1 p.2).symm
  rw [heq]
  apply (trace_measurable P A U hb hc hQ H).comp
  simpa only [StaticGaussianSampler.sample, one_smul] using
    (StaticGaussianSampler.sample_measurable (protocol (H := H) P A U hb hc hQ).original 1 H).fst

theorem true_trace_law (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (hτ : ∀ i, 0 < P.disclosure i) (hr : 1 ≤ P.r) (hσ₃ : P.σ₃ ≠ 0) (hσ₄ : P.σ₄ ≠ 0)
    (νR : Measure Rot) (νS : Measure Seed) [IsProbabilityMeasure νR] [IsProbabilityMeasure νS] :
    (trueLaw (protocol (H := H) P A U hb hc hQ) 1 (νR.prod νS) H).map (trace (H := H) P A U H) =
      ((νR.prod νS).prod (standardGaussian (jointDim d))).map (directTrace P A U H) := by
  rw [← StaticGaussianSampler.trueLaw_sample (protocol (H := H) P A U hb hc hQ) 1 (νR.prod νS) H]
  have hm : Measurable (fun p : (Rot × Seed) × Vec (jointDim d) =>
      StaticGaussianSampler.run (protocol (H := H) P A U hb hc hQ).original.rowProtocol.rows
        p.1 ((protocol (H := H) P A U hb hc hQ).original.signal p.1 + (1 : ℝ) • p.2) H) :=
    (StaticGaussianSampler.sample_measurable (protocol (H := H) P A U hb hc hQ).original 1 H).fst
  rw [Measure.map_map (trace_measurable P A U hb hc hQ H) hm]
  congr 1
  funext p
  simp only [Function.comp_apply, one_smul]
  exact static_trace_exact P A U hτ hr hσ₃ hσ₄ p.1 p.2

end MatchingBounds1005.SourceReferenceReplay

