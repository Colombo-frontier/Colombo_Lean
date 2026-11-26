import ModelFull

/-! Independent sample tapes, pathwise legality and the fixed-instance expected
error contract. No performance conclusion is a field or assumption here. -/

open MeasureTheory

namespace Task006.Full

universe u v

noncomputable def iidHandleLaw {Ω : Type v} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : Measure (ℕ → Ω) :=
  Measure.infinitePi (fun _ : ℕ => μ)

instance iidHandleLaw_isProbability {Ω : Type v} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : IsProbabilityMeasure (iidHandleLaw μ) := by
  unfold iidHandleLaw
  infer_instance

noncomputable def optimalValue {d : ℕ} {L R : ℝ} {Ω : Type v} [MeasurableSpace Ω]
    {μ : Measure Ω} (I : SampleInstance d L R Ω μ) : ℝ :=
  sInf (I.objective '' outputDomain d R)

namespace OracleAlgorithm

variable {d N : ℕ} {S : Type u} [MeasurableSpace S]
variable {Ω : Type v} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable def realizedOutput (A : OracleAlgorithm d N S)
    (F : Space d → Ω → ℝ) (w : S × (ℕ → Ω)) : Space d :=
  A.output w.1 (A.finalTranscript F w.2 w.1)

noncomputable def realizedGap {L R : ℝ} (A : OracleAlgorithm d N S)
    (I : SampleInstance d L R Ω μ) (w : S × (ℕ → Ω)) : ℝ :=
  I.objective (A.realizedOutput I.sample w) - optimalValue I

/-- A guarantee for this fixed instance: the same budget/handle/domain contract
holds on every path, and expectation is over independent private seed and i.i.d.
handles. Integrability is explicit to avoid totalized-integral loopholes. -/
def SolvesInstance {L R : ℝ} (eps : ℝ) (A : OracleAlgorithm d N S)
    (σ : Measure S) (I : SampleInstance d L R Ω μ) [IsProbabilityMeasure μ] : Prop :=
  (∀ seed tape, A.executionLegal I.sample tape seed R) ∧
  Integrable (A.realizedGap I) (σ.prod (iidHandleLaw μ)) ∧
  (∫ w, A.realizedGap I w ∂(σ.prod (iidHandleLaw μ))) ≤ eps

end OracleAlgorithm

/-- The exact parameter regime in Theorem 1. -/
def Regime (d : ℕ) (L R eps : ℝ) : Prop :=
  2 ≤ d ∧ 0 < L ∧ 0 < R ∧ 0 < eps ∧
  max (d : ℝ) (2 ^ 17 : ℝ) ≤ L * R / eps

/-- Uniformity ranges over sample probability spaces and fixed admissible
instances, rather than choosing a different algorithm for each sample family. -/
def UniformlySolves {d N : ℕ} {S : Type u} [MeasurableSpace S]
    (L R eps : ℝ) (σ : Measure S) (A : OracleAlgorithm d N S) : Prop :=
  ∀ (Ω : Type v) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ)
    (hμ : @IsProbabilityMeasure Ω mΩ μ)
    (I : @SampleInstance d L R Ω mΩ μ),
    @OracleAlgorithm.SolvesInstance d N S _ Ω mΩ μ L R eps A σ I hμ

/-- Existence of one public-parameter policy and private random seed law with a
uniform fixed-instance guarantee. The quantifier order is part of the model. -/
def AdmitsBudget (d N : ℕ) (L R eps : ℝ) : Prop :=
  ∃ (S : Type u) (mS : MeasurableSpace S) (σ : @Measure S mS)
    (_hσ : @IsProbabilityMeasure S mS σ) (A : @OracleAlgorithm d N S mS),
    @UniformlySolves.{u,v} d N S mS L R eps σ A

noncomputable def minimaxReplies (d : ℕ) (L R eps : ℝ) : ℕ :=
  sInf {N : ℕ | AdmitsBudget.{u,v} d N L R eps}

end Task006.Full
