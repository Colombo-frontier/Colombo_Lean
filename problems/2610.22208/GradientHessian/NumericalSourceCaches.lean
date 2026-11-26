import GradientHessian.NumericalPreloadTransparency
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
namespace GradientHessian.NumericalSourceCaches
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

def input (j : Fin (4096*J^2+1)) (x : RawHierarchy.Raw d n r J E H t × Seed) :
    ForkMachineBound.Input d n r (RawNumericalExperiment.Auxiliary d n r J E H t Seed) PUnit.{1} :=
  RawNumericalExperiment.factor t ((leafEquiv t).symm leaf) j x

def preCache (j : Fin (4096*J^2+1)) (x : RawHierarchy.Raw d n r J E H t × Seed) : Cache d J :=
  (NumericalPreprocessor.forcing B j (input t leaf j x).1.2.1,
    (NumericalPriorCache.store B j (ForkMachineBound.earlierReadout J P fallback (input t leaf j x))
      (input t leaf j x).1.2.1).2)

def postCache (j : Fin (4096*J^2+1)) (x : RawHierarchy.Raw d n r J E H t × Seed) : Cache d J :=
  (Function.update (preCache P B fallback t leaf j x).1 j
    (InverseGate.H₀ • LowRank.matrixEuclideanMap B (input t leaf j x).2.1),
    (preCache P B fallback t leaf j x).2)

theorem matrix_eq (j : Fin (4096*J^2+1)) (x : RawHierarchy.Raw d n r J E H t × Seed) :
    ForkMachineBound.sourceA J P (input t leaf j x)=
      MatrixGoodSpectrum.sourceMatrix P J (RawLeafFactor.leafNumerical t x.1 ((leafEquiv t).symm leaf)).1 := by
  rw [ForkMachineBound.sourceA,input,RawNumericalExperiment.factor_matrix]

theorem readout_eq (j : Fin (4096*J^2+1)) (x : RawHierarchy.Raw d n r J E H t × Seed) :
    ForkMachineBound.earlierReadout J P fallback (input t leaf j x)=
      ReadoutOracle.readout (ReadoutFilter.matrixUpper J) P
        (MatrixGoodSpectrum.sourceMatrix P J (RawLeafFactor.leafNumerical t x.1 ((leafEquiv t).symm leaf)).1) fallback := by
  rw [ForkMachineBound.earlierReadout,matrix_eq]

theorem pre_forcing (j k : Fin (4096*J^2+1)) (x : RawHierarchy.Raw d n r J E H t × Seed) (hk : k<j) :
    (preCache P B fallback t leaf j x).1 k=
      (atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x.1)).2.1 k :=
  NumericalPriorCache.forcing_exact P B fallback t _ j k x (ne_of_lt hk)

theorem pre_readout (j k : Fin (4096*J^2+1)) (x : RawHierarchy.Raw d n r J E H t × Seed) (hk : k<j) :
    (preCache P B fallback t leaf j x).2 k=
      (atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x.1)).2.2.1 k := by
  change (NumericalPriorCache.store B j (ForkMachineBound.earlierReadout J P fallback (input t leaf j x))
      (input t leaf j x).1.2.1).2 k=_
  rw [readout_eq]
  exact NumericalPriorCache.prior_value_exact.{_,1} P B fallback t _ j k x hk

theorem pre_zero (j : Fin (4096*J^2+1)) (x : RawHierarchy.Raw d n r J E H t × Seed) :
    (preCache P B fallback t leaf j x).2 j=0 := NumericalPriorCache.store_target_zero B j _ _

theorem post_forcing (j : Fin (4096*J^2+1)) (x : RawHierarchy.Raw d n r J E H t × Seed) :
    (postCache P B fallback t leaf j x).1=
      (atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x.1)).2.1 :=
  NumericalPriorCache.supplied_forcing_exact.{_,1,1} P B fallback t _ j x

theorem post_readout (j k : Fin (4096*J^2+1)) (x : RawHierarchy.Raw d n r J E H t × Seed) (hk : k<j) :
    (postCache P B fallback t leaf j x).2 k=
      (atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x.1)).2.2.1 k :=
  pre_readout P B fallback t leaf j k x hk

theorem post_zero (j : Fin (4096*J^2+1)) (x : RawHierarchy.Raw d n r J E H t × Seed) :
    (postCache P B fallback t leaf j x).2 j=0 := pre_zero P B fallback t leaf j x

theorem external_eq (j : Fin (4096*J^2+1)) (x : RawHierarchy.Raw d n r J E H t × Seed) :
    (input t leaf j x).1.2.2.1=(RawLeafFactor.factor t ((leafEquiv t).symm leaf) x.1).2 := rfl

theorem seed_eq (j : Fin (4096*J^2+1)) (x : RawHierarchy.Raw d n r J E H t × Seed) :
    (input t leaf j x).1.2.2.2=x.2 := rfl

theorem target_readout (j : Fin (4096*J^2+1)) (x : RawHierarchy.Raw d n r J E H t × Seed) :
    UnmarkedReadout.sourceOutput J P (input t leaf j x).1.1 B fallback (input t leaf j x).2.1=
      (leafCoefficients (RawHierarchy.assemble P B fallback t x.1) leaf).a j := by
  rw [input,RawNumericalExperiment.factor_matrix,RawNumericalExperiment.factor_mark]
  change _=(leafData t (RawHierarchy.assemble P B fallback t x.1) ((leafEquiv t).symm leaf)).a j
  rw [RawLeafFactor.leaf_a_assemble]

theorem loaded_cache (j : Fin (4096*J^2+1)) (cutoff : ℕ) (x : RawHierarchy.Raw d n r J E H t × Seed) :
    NumericalPreprocessor.cache B t j (NumericalPreloadTransparency.loaded (ell := ell) B t policy j
      (ForkMachineBound.earlierReadout J P fallback (input t leaf j x)) cutoff (input t leaf j x).1.2)=
      preCache P B fallback t leaf j x := rfl

theorem saved_cache (K : ℝ) (j : Fin (4096*J^2+1)) (cutoff N : ℕ)
    (x : RawHierarchy.Raw d n r J E H t × Seed) :
    NumericalPreprocessor.cache B t j (NumericalPreloadTransparency.savedRuntime (ell := ell) P B fallback t leaf policy K j
      (ForkMachineBound.sourceA J P (input t leaf j x))
      (ForkMachineBound.earlierReadout J P fallback (input t leaf j x)) cutoff (input t leaf j x).1.2 N)=
      preCache P B fallback t leaf j x := rfl

theorem post_saved_cache (K : ℝ) (j : Fin (4096*J^2+1)) (cutoff N : ℕ)
    (x : RawHierarchy.Raw d n r J E H t × Seed) :
    NumericalPostprocessor.cache B t j (NumericalPostprocessor.initial t
      (NumericalPreloadTransparency.savedRuntime (ell := ell) P B fallback t leaf policy K j
        (ForkMachineBound.sourceA J P (input t leaf j x))
        (ForkMachineBound.earlierReadout J P fallback (input t leaf j x)) cutoff (input t leaf j x).1.2 N)
      (input t leaf j x).2.1)=postCache P B fallback t leaf j x := rfl

end GradientHessian.NumericalSourceCaches
