import SecondOrder.CurvatureFrontierInformation
import SecondOrder.SampledResponseKernel

open MeasureTheory InformationTheory ProbabilityTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section
variable {m T k : ℕ}

theorem curvatureTruncatedReply_continuous (Θ : Fin (T+1) → BalancedVector m) {R : ℝ}
    (z : CurvatureCoefficients m T R) (k : ℕ) : Continuous (curvatureTruncatedReply Θ z k) := by
  have hf := curvatureTruncatedLoss_contDiff Θ z k
  have hg : ContDiff ℝ 1 (gradient (curvatureTruncatedLoss Θ z k)) :=
    (InnerProductSpace.toDual ℝ (CurvatureSpace m T)).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 3 by decide))
  exact hf.continuous.prodMk (hg.continuous.prodMk (hg.continuous_fderiv (by norm_num)))

theorem curvatureTruncatedReply_measurable (Θ : Fin (T+1) → BalancedVector m) (R : ℝ) (k : ℕ) :
    Measurable (fun w : CurvatureSpace m T × CurvatureCoefficients m T R =>
      curvatureTruncatedReply Θ w.2 k w.1) :=
  measurable_from_prod_countable (fun z => (curvatureTruncatedReply_continuous Θ z k).measurable)

theorem curvatureFrontierReply_measurable (θ₀ : BalancedVector m) (pastΘ : Fin k → BalancedVector m)
    (R : ℝ) : Measurable (fun w : CurvatureSpace m T ×
      (CurvaturePastCoefficients m k R × (UpperPair (2*m) → SignedCoefficient R)) =>
      curvatureFrontierReply θ₀ pastΘ w.1 w.2) :=
  measurable_from_prod_countable (fun a =>
    (curvatureTruncatedReply_continuous (extendHiddenPrefix θ₀ pastΘ)
      (extendCoefficientPrefix a.1 a.2) k).measurable)

def curvatureExtendedKernel (Θ : Fin (T+1) → BalancedVector m) (R : ℝ) (hR : 2≤R) (k : ℕ) :
    Kernel (CurvatureSpace m T) (CurvatureRichResponse m T) :=
  sampledResponseKernel (curvatureCoefficientLaw Θ R hR).toMeasure
    (fun x z => curvatureTruncatedReply Θ z k x) (curvatureTruncatedReply_measurable Θ R k)

def curvatureReferenceKernel (θ₀ : BalancedVector m) (pastΘ : Fin k → BalancedVector m)
    (R : ℝ) (hR : 2≤R) : Kernel (CurvatureSpace m T) (CurvatureRichResponse m T) :=
  sampledResponseKernel ((curvaturePastCoefficientLaw pastΘ R hR).toMeasure.prod
    (finitePiPMF (fun _ : UpperPair (2*m) => fairCoefficientPMF R hR)).toMeasure)
      (curvatureFrontierReply θ₀ pastΘ) (curvatureFrontierReply_measurable θ₀ pastΘ R)

instance curvatureExtendedKernel_markov (Θ : Fin (T+1) → BalancedVector m)
    (R : ℝ) (hR : 2≤R) (k : ℕ) : IsMarkovKernel (curvatureExtendedKernel Θ R hR k) :=
  inferInstanceAs (IsMarkovKernel (sampledResponseKernel _ _ _))

instance curvatureReferenceKernel_markov (θ₀ : BalancedVector m) (pastΘ : Fin k → BalancedVector m)
    (R : ℝ) (hR : 2≤R) : IsMarkovKernel (curvatureReferenceKernel (T := T) θ₀ pastΘ R hR) :=
  inferInstanceAs (IsMarkovKernel (sampledResponseKernel _ _ _))

theorem curvatureReferenceKernel_apply (θ₀ : BalancedVector m) (pastΘ : Fin k → BalancedVector m)
    (R : ℝ) (hR : 2≤R) (x : CurvatureSpace m T) :
    curvatureReferenceKernel θ₀ pastΘ R hR x = curvatureFrontierReferenceLaw θ₀ pastΘ R hR x := rfl

/-- The reference is a Markov kernel, independent of the fresh hidden block,
and the information bound holds uniformly at every query, even off the frontier. -/
theorem curvatureExtendedKernel_kl (Θ : Fin (T+1) → BalancedVector m) (θ₀ : BalancedVector m)
    (R : ℝ) (hR : 2≤R) (hk : k≤T) (x : CurvatureSpace m T) :
    klDiv (curvatureExtendedKernel Θ R hR k x)
      (curvatureReferenceKernel θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩) R hR x) ≤
      ENNReal.ofReal ((((2*m:ℕ):ℝ)*(((2*m:ℕ):ℝ)-1))/(2*R^2)) :=
  curvatureTruncatedReply_frontier_kl Θ θ₀ R hR hk x

end
end SecondOrder
