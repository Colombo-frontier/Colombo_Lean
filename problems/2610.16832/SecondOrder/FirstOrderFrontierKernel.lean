import SecondOrder.FirstOrderFrontierInformation
import SecondOrder.SampledResponseKernel

open MeasureTheory InformationTheory ProbabilityTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section
variable {d T k : ℕ}

theorem firstOrderTruncatedReply_continuous (Θ : Fin (T+1) → (Fin d → Bool)) {R : ℝ}
    (z : FirstOrderCoefficients d T R) (k : ℕ) : Continuous (firstOrderTruncatedReply Θ z k) := by
  have hf := firstOrderTruncatedLoss_contDiff Θ z k
  have hg : ContDiff ℝ 1 (gradient (firstOrderTruncatedLoss Θ z k)) :=
    (InnerProductSpace.toDual ℝ (FirstOrderSpace d T)).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 3 by decide))
  exact hf.continuous.prodMk (hg.continuous.prodMk (hg.continuous_fderiv (by norm_num)))

theorem firstOrderTruncatedReply_measurable (Θ : Fin (T+1) → (Fin d → Bool)) (R : ℝ) (k : ℕ) :
    Measurable (fun w : FirstOrderSpace d T × FirstOrderCoefficients d T R =>
      firstOrderTruncatedReply Θ w.2 k w.1) :=
  measurable_from_prod_countable (fun z => (firstOrderTruncatedReply_continuous Θ z k).measurable)

theorem firstOrderFrontierReply_measurable (θ₀ : (Fin d → Bool)) (pastΘ : Fin k → (Fin d → Bool))
    (R : ℝ) : Measurable (fun w : FirstOrderSpace d T ×
      (FirstOrderPastCoefficients d k R × (Fin d → SignedCoefficient R)) =>
      firstOrderFrontierReply θ₀ pastΘ w.1 w.2) :=
  measurable_from_prod_countable (fun a =>
    (firstOrderTruncatedReply_continuous (firstOrderExtendHiddenPrefix θ₀ pastΘ)
      (firstOrderExtendCoefficientPrefix a.1 a.2) k).measurable)

def firstOrderExtendedKernel (Θ : Fin (T+1) → (Fin d → Bool)) (R : ℝ) (hR : 2≤R) (k : ℕ) :
    Kernel (FirstOrderSpace d T) (FirstOrderRichResponse d T) :=
  sampledResponseKernel (firstOrderChainCoefficientLaw Θ R hR).toMeasure
    (fun x z => firstOrderTruncatedReply Θ z k x) (firstOrderTruncatedReply_measurable Θ R k)

def firstOrderReferenceKernel (θ₀ : (Fin d → Bool)) (pastΘ : Fin k → (Fin d → Bool))
    (R : ℝ) (hR : 2≤R) : Kernel (FirstOrderSpace d T) (FirstOrderRichResponse d T) :=
  sampledResponseKernel ((firstOrderPastCoefficientLaw pastΘ R hR).toMeasure.prod
    (finitePiPMF (fun _ : Fin d => fairCoefficientPMF R hR)).toMeasure)
      (firstOrderFrontierReply θ₀ pastΘ) (firstOrderFrontierReply_measurable θ₀ pastΘ R)

instance firstOrderExtendedKernel_markov (Θ : Fin (T+1) → (Fin d → Bool))
    (R : ℝ) (hR : 2≤R) (k : ℕ) : IsMarkovKernel (firstOrderExtendedKernel Θ R hR k) :=
  inferInstanceAs (IsMarkovKernel (sampledResponseKernel _ _ _))

instance firstOrderReferenceKernel_markov (θ₀ : (Fin d → Bool)) (pastΘ : Fin k → (Fin d → Bool))
    (R : ℝ) (hR : 2≤R) : IsMarkovKernel (firstOrderReferenceKernel (T := T) θ₀ pastΘ R hR) :=
  inferInstanceAs (IsMarkovKernel (sampledResponseKernel _ _ _))

theorem firstOrderReferenceKernel_apply (θ₀ : (Fin d → Bool)) (pastΘ : Fin k → (Fin d → Bool))
    (R : ℝ) (hR : 2≤R) (x : FirstOrderSpace d T) :
    firstOrderReferenceKernel θ₀ pastΘ R hR x = firstOrderFrontierReferenceLaw θ₀ pastΘ R hR x := rfl

/-- The reference is a Markov kernel, independent of the fresh hidden block,
and the information bound holds uniformly at every query, even off the frontier. -/
theorem firstOrderExtendedKernel_kl (Θ : Fin (T+1) → (Fin d → Bool)) (θ₀ : (Fin d → Bool))
    (R : ℝ) (hR : 2≤R) (hk : k≤T) (x : FirstOrderSpace d T) :
    klDiv (firstOrderExtendedKernel Θ R hR k x)
      (firstOrderReferenceKernel θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩) R hR x) ≤
      ENNReal.ofReal ((d:ℝ)/R^2) :=
  firstOrderTruncatedReply_frontier_kl Θ θ₀ R hR hk x

end
end SecondOrder

