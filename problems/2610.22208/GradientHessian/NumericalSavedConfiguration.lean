import GradientHessian.NumericalSourceCaches
import GradientHessian.NumericalCachedEarlyPhase
import GradientHessian.NumericalPreSupplyEquality
import GradientHessian.NumericalSupplySplit
import GradientHessian.NumericalPostEndpoint
import GradientHessian.NumericalPostprocessor
import GradientHessian.NumericalMaskedDriverEquality
import GradientHessian.ControllerExternalReceiptCongruence
import GradientHessian.NumericalPreloadExecution
import GradientHessian.NumericalRuleAgreement
import GradientHessian.NumericalRichAgreement
import GradientHessian.ControllerReceiptCongruence
import GradientHessian.NumericalProductStep
import GradientHessian.NumericalRuntime
import GradientHessian.NumericalOrdinaryProcedure
noncomputable section
namespace GradientHessian.NumericalSavedConfiguration
open Matrix
open Classical HigherHierarchy HierarchyAddresses CensoredHierarchy FrontierState TaskState
  ComparisonController ComparisonControllerReplay ControllerMeasurable ControllerPolicyDriver
  GeometricRepair NumericalCachedOracle

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (leaf : Leaf (t+1))
variable [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (policy : Machine.Policy Seed S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
  (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))
  (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ)))

open NumericalCoefficientPatch CensoredOracle

open NumericalSourceCaches ControllerDriverMonotonicity ControllerDriverResource TaskSlots VisibilityTaskWindow
  ControllerNormalRealization

theorem saved_config {K : ℝ} (hK : 0<K) (hell : 0<ell)
    (x : RawHierarchy.Raw d n r J E H t × Seed) (N k : ℕ) (j : Fin (4096*J^2+1)) :
    (NumericalPreloadTransparency.savedRuntime (ell := ell) P B fallback t leaf policy K j
      (ForkMachineBound.sourceA J P (input t leaf j x))
      (ForkMachineBound.earlierReadout J P fallback (input t leaf j x)) N (input t leaf j x).1.2 k).2.2=
    (NumericalPreloadExecution.externalStep P B fallback t leaf policy K j
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x.1).2 (postCache P B fallback t leaf j x)
      (MatrixGoodSpectrum.sourceMatrix P J (RawLeafFactor.leafNumerical t x.1 ((leafEquiv t).symm leaf)).1))^[k]
        (ControllerPolicyDriver.initial policy N x.2 (TaskState.initial (ell := ell))) := by
  change (NumericalPreloadExecution.externalStep P B fallback t leaf policy K j
    (input t leaf j x).1.2.2.1 (preCache P B fallback t leaf j x)
    (ForkMachineBound.sourceA J P (input t leaf j x)))^[k]
      (ControllerPolicyDriver.initial policy N (input t leaf j x).1.2.2.2 TaskState.initial)=_
  rw [external_eq t leaf j x,seed_eq t leaf j x,matrix_eq P t leaf j x]
  exact NumericalPreSupplyEquality.external_caches_initial P B fallback t leaf policy hK hell x.1
    (preCache P B fallback t leaf j x) (postCache P B fallback t leaf j x) j
    (fun q hq => pre_forcing P B fallback t leaf j q x hq)
    (fun q hq => pre_readout P B fallback t leaf j q x hq)
    (fun q _ => congrFun (post_forcing P B fallback t leaf j x) q)
    (fun q hq => post_readout P B fallback t leaf j q x hq) k N x.2

end GradientHessian.NumericalSavedConfiguration
