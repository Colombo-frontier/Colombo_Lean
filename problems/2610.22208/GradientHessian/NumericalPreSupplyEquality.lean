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
namespace GradientHessian.NumericalPreSupplyEquality
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

open NumericalCoefficientPatch CensoredOracle NumericalShadowRules GeometricMaskedEarly
  ControllerDriverMonotonicity ControllerReceiptCongruence ControllerExternalReceiptCongruence
  TaskSlots VisibilityWindow VisibilityTaskWindow

theorem external_eq_source {K : ℝ} (hK : 0<K) (hell : 0<ell)
    (x : RawHierarchy.Raw d n r J E H t) (c : Cache d J) (j : Fin (4096*J^2+1))
    (hb : ∀ k,k<j → c.1 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.1 k)
    (ha : ∀ k,k<j → c.2 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.2.1 k)
    (N : ℕ)
    (q : Config (t+1) (4096*J^2+1) ell S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
      (Action t (4096*J^2)))
    (hc : Coherent (markSupplied leaf j) q)
    (hq : Receipt (shadowRules P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c) q) :
    (NumericalPreloadExecution.externalStep P B fallback t leaf policy K j
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c
      (MatrixGoodSpectrum.sourceMatrix P J (RawLeafFactor.leafNumerical t x ((leafEquiv t).symm leaf)).1))^[N] q =
    (external policy (suppress (rules K (RawHierarchy.assemble P B fallback t x)) (blockLeaf leaf))
      (markSupplied leaf j) NumericalDriverInstructions.finished
      (CensoredPolicy.ordinaryReply K t (RawHierarchy.coefficients P B fallback t x))
      (CensoredPolicy.richReply K t (RawHierarchy.coefficients P B fallback t x)))^[N] q := by
  have hread := NumericalMaskedDriverEquality.cached_readouts P B fallback t leaf x c j ha
  change (external policy
    (shadowRules P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c)
    (markSupplied leaf j) NumericalDriverInstructions.finished
    (NumericalProductStep.ordinary P B fallback t leaf K
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c
      (MatrixGoodSpectrum.sourceMatrix P J (RawLeafFactor.leafNumerical t x ((leafEquiv t).symm leaf)).1))
    (NumericalPolicyReplies.rich P B fallback t leaf K
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c))^[N] q = _
  apply external_iterate_congr policy
  · rfl
  · rfl
  · intro s hs Z a
    exact (NumericalRuleAgreement.pre_rules P B fallback t leaf K x c j hread s hs Z).2.2.1 a
  · intro s hs Z
    exact (NumericalRuleAgreement.pre_rules P B fallback t leaf K x c j hread s hs Z).2.2.2
  · intro before after hsb _ Z
    have he := NumericalCacheReplyAgreement.ordinary_before_supply P B fallback t leaf hK x c j
      hb ha before after hsb Z
    rw [NumericalPriorCache.coefficient_A] at he
    exact he
  · intro p before after hk he _ hsa
    exact NumericalRichAgreement.rich_before_supply P B fallback t leaf hK x c j _ p hk before after he hsa
  · exact hell
  · intro s hs p hstop
    exact GeometricRepair.markSupplied_completed_mono leaf j s _ (normal_completed_mono _ p hs) hstop
  · exact hc
  · exact hq

theorem external_caches_initial {K : ℝ} (hK : 0<K) (hell : 0<ell)
    (x : RawHierarchy.Raw d n r J E H t) (c c' : Cache d J) (j : Fin (4096*J^2+1))
    (hb : ∀ k,k<j → c.1 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.1 k)
    (ha : ∀ k,k<j → c.2 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.2.1 k)
    (hb' : ∀ k,k<j → c'.1 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.1 k)
    (ha' : ∀ k,k<j → c'.2 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.2.1 k)
    (N cutoff : ℕ) (seed : Seed) :
    (NumericalPreloadExecution.externalStep P B fallback t leaf policy K j
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c
      (MatrixGoodSpectrum.sourceMatrix P J (RawLeafFactor.leafNumerical t x ((leafEquiv t).symm leaf)).1))^[N]
      (ControllerPolicyDriver.initial policy cutoff seed (TaskState.initial (ell := ell))) =
    (NumericalPreloadExecution.externalStep P B fallback t leaf policy K j
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c'
      (MatrixGoodSpectrum.sourceMatrix P J (RawLeafFactor.leafNumerical t x ((leafEquiv t).symm leaf)).1))^[N]
      (ControllerPolicyDriver.initial policy cutoff seed (TaskState.initial (ell := ell))) := by
  exact (external_eq_source P B fallback t leaf policy hK hell x c j hb ha N
    (ControllerPolicyDriver.initial policy cutoff seed TaskState.initial) (initial_ready hell) trivial).trans
    (external_eq_source P B fallback t leaf policy hK hell x c' j hb' ha' N
      (ControllerPolicyDriver.initial policy cutoff seed TaskState.initial) (initial_ready hell) trivial).symm

end GradientHessian.NumericalPreSupplyEquality
