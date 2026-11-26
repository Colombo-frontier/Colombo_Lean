import SecondOrder.ConservativeFrontierInformation
import SecondOrder.SampledResponseKernel

open MeasureTheory InformationTheory ProbabilityTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

theorem scalarRichResponse_measurable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] {f : H → ℝ} (hf : ContDiff ℝ 2 f) :
    Measurable (scalarRichResponse f) := by
  have hg : ContDiff ℝ 1 (gradient f) :=
    (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num))
  exact hf.continuous.measurable.prodMk
    (hg.continuous.measurable.prodMk (hg.continuous_fderiv (by norm_num)).measurable)

variable {T m : ℕ} {E : Fin (T+1) → Type*} {Θ : Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)]
  [MeasurableSpace (PiLp 2 E)] [BorelSpace (PiLp 2 E)]

namespace ConservativeFeatureData

theorem truncatedReply_measurable (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ : Fin (T+1) → Θ)
    (hreg : ContDiff ℝ 2 reg) (h0 : ∀ i, ContDiff ℝ 2 (D.offset i))
    (hφ : ∀ i a, ContDiff ℝ 2 (D.feature i a)) (hgate : ∀ i θ, ContDiff ℝ 2 (gate i θ))
    (R : ℝ) (k : ℕ) :
    Measurable (fun w : PiLp 2 E × (Fin (T+1) → Fin m → SignedCoefficient R) =>
      D.truncatedReply reg gate θ w.2 k w.1) :=
  measurable_from_prod_countable (fun z => scalarRichResponse_measurable
    (D.truncatedLoss_contDiff reg gate θ hreg h0 hφ hgate z k))

theorem frontierReply_measurable (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ₀ : Θ) {k : ℕ} (pastθ : Fin k → Θ)
    (hreg : ContDiff ℝ 2 reg) (h0 : ∀ i, ContDiff ℝ 2 (D.offset i))
    (hφ : ∀ i a, ContDiff ℝ 2 (D.feature i a)) (hgate : ∀ i θ, ContDiff ℝ 2 (gate i θ))
    (R : ℝ) :
    Measurable (fun w : PiLp 2 E × ((Fin k → Fin m → SignedCoefficient R) × (Fin m → SignedCoefficient R)) =>
      D.frontierReply reg gate θ₀ pastθ w.1 w.2) :=
  measurable_from_prod_countable (fun a => scalarRichResponse_measurable
    (D.truncatedLoss_contDiff reg gate (conservativeExtendHidden θ₀ pastθ) hreg h0 hφ hgate
      (conservativeExtendCoefficients a.1 a.2) k))

def extendedKernel (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ : Fin (T+1) → Θ)
    (hreg : ContDiff ℝ 2 reg) (h0 : ∀ i, ContDiff ℝ 2 (D.offset i))
    (hφ : ∀ i a, ContDiff ℝ 2 (D.feature i a)) (hgate : ∀ i θ, ContDiff ℝ 2 (gate i θ))
    (R : ℝ) (hR : 2 ≤ R) (k : ℕ) : Kernel (PiLp 2 E) (ScalarRichResponse (PiLp 2 E)) :=
  sampledResponseKernel (D.arrayLaw θ R hR).toMeasure (fun x z => D.truncatedReply reg gate θ z k x)
    (D.truncatedReply_measurable reg gate θ hreg h0 hφ hgate R k)

/-- A genuine Markov reference kernel indexed only by past hidden blocks. -/
def referenceKernel (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ₀ : Θ) {k : ℕ} (hk : k ≤ T) (pastθ : Fin k → Θ)
    (hreg : ContDiff ℝ 2 reg) (h0 : ∀ i, ContDiff ℝ 2 (D.offset i))
    (hφ : ∀ i a, ContDiff ℝ 2 (D.feature i a)) (hgate : ∀ i θ, ContDiff ℝ 2 (gate i θ))
    (R : ℝ) (hR : 2 ≤ R) : Kernel (PiLp 2 E) (ScalarRichResponse (PiLp 2 E)) :=
  sampledResponseKernel ((D.pastLaw hk pastθ R hR).toMeasure.prod
    (finitePiPMF (fun _ : Fin m => fairCoefficientPMF R hR)).toMeasure)
    (D.frontierReply reg gate θ₀ pastθ) (D.frontierReply_measurable reg gate θ₀ pastθ hreg h0 hφ hgate R)

instance extendedKernel_markov (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ : Fin (T+1) → Θ)
    (hreg : ContDiff ℝ 2 reg) (h0 : ∀ i, ContDiff ℝ 2 (D.offset i))
    (hφ : ∀ i a, ContDiff ℝ 2 (D.feature i a)) (hgate : ∀ i θ, ContDiff ℝ 2 (gate i θ))
    (R : ℝ) (hR : 2 ≤ R) (k : ℕ) :
    IsMarkovKernel (D.extendedKernel reg gate θ hreg h0 hφ hgate R hR k) :=
  inferInstanceAs (IsMarkovKernel (sampledResponseKernel _ _ _))

instance referenceKernel_markov (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ₀ : Θ) {k : ℕ} (hk : k ≤ T) (pastθ : Fin k → Θ)
    (hreg : ContDiff ℝ 2 reg) (h0 : ∀ i, ContDiff ℝ 2 (D.offset i))
    (hφ : ∀ i a, ContDiff ℝ 2 (D.feature i a)) (hgate : ∀ i θ, ContDiff ℝ 2 (gate i θ))
    (R : ℝ) (hR : 2 ≤ R) :
    IsMarkovKernel (D.referenceKernel reg gate θ₀ hk pastθ hreg h0 hφ hgate R hR) :=
  inferInstanceAs (IsMarkovKernel (sampledResponseKernel _ _ _))

end ConservativeFeatureData
end
end SecondOrder
