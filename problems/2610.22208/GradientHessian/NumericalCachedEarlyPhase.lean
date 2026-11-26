import GradientHessian.NumericalMaskedDriverEquality
import GradientHessian.NumericalEarlyExpectation
import GradientHessian.ControllerGuardedReverse
import GradientHessian.NumericalRuleAgreement
import GradientHessian.NumericalRichAgreement
import GradientHessian.ControllerReceiptCongruence
import GradientHessian.NumericalProductStep
import GradientHessian.NumericalRuntime
import GradientHessian.NumericalOrdinaryProcedure
noncomputable section
namespace GradientHessian.NumericalCachedEarlyPhase
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
  ControllerDriverMonotonicity ControllerNormalRealization

theorem early_phase {K : ℝ} (hK : 0<K) (hell : 0<ell)
    (x : RawHierarchy.Raw d n r J E H t) (hd : Valid _ _ _ _ t (RawHierarchy.assemble P B fallback t x))
    (c : Cache d J) (j : Fin (4096*J^2+1))
    (hb : ∀ k,k≤j → c.1 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.1 k)
    (ha : ∀ k,k<j → c.2 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.2.1 k)
    (hz : c.2 j=0) (N : ℕ) (seed : Seed)
    (he : (x,seed)∈NumericalEarlyExpectation.earlyEvent (ell := ell) P B fallback t leaf policy K N j) :
    ∃ i<(N+1)*(8^(t+1)+4),∃ rem a output p s,
      ControllerPolicyDriver.run (ell := ell) policy
        (shadowRules P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c)
        (fun _ => false)
        (NumericalProductStep.ordinary P B fallback t leaf K
          (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c
          (MatrixGoodSpectrum.sourceMatrix P J (RawLeafFactor.leafNumerical t x ((leafEquiv t).symm leaf)).1))
        (NumericalPolicyReplies.rich P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c)
        i (ControllerPolicyDriver.initial policy N seed TaskState.initial)=
          .pending rem a output (.normal p s) ∧
      IsEarlyFor (rules K (RawHierarchy.assemble P B fallback t x)) p s (leaf,j) ∧
      taskDisclosed leaf j s=false := by
  have hd' : Valid _ _ _ _ t (HierarchyParameters.decode t (RawHierarchy.coefficients P B fallback t x)) := by
    rwa [RawHierarchy.decode_coefficients]
  have he' : 0<ControllerEarlyEvents.count
      (rules (ell := ell) K (HierarchyParameters.decode t (RawHierarchy.coefficients P B fallback t x)))
      (ControllerPolicyTrace.withOutput policy
        (JetLocality.ordinaryJet (scalar K t (HierarchyParameters.decode t (RawHierarchy.coefficients P B fallback t x))))
        (JetLocality.richJet (scalar K t (HierarchyParameters.decode t (RawHierarchy.coefficients P B fallback t x))))
        N seed) TaskState.initial (leaf,j) := by
    rw [RawHierarchy.decode_coefficients]
    exact he
  obtain ⟨i,hi,rem,a,output,p,s,hm,hearly,hstop⟩ :=
    GeometricMaskedEarly.original_early_has_masked_normal_phase t policy hK
      (RawHierarchy.coefficients P B fallback t x) hd' hell N seed leaf j he'
  simp only [RawHierarchy.decode_coefficients] at hm hearly
  have hc := NumericalMaskedDriverEquality.run_eq (ell := ell) P B fallback t leaf policy hK x c j hb ha hz i
    (ControllerPolicyDriver.initial policy N seed TaskState.initial) (by trivial)
  rw [hm] at hc
  have hrev := ControllerGuardedReverse.run_eq_of_open_endpoint policy
    (shadowRules P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c)
    (taskDisclosed leaf j)
    (NumericalProductStep.ordinary P B fallback t leaf K
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c
      (MatrixGoodSpectrum.sourceMatrix P J (RawLeafFactor.leafNumerical t x ((leafEquiv t).symm leaf)).1))
    (NumericalPolicyReplies.rich P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c)
    i (ControllerPolicyDriver.initial policy N seed TaskState.initial) (by trivial)
    (by rw [hc]; exact hstop)
  exact ⟨i,hi,rem,a,output,p,s,hrev.symm.trans hc,hearly,hstop⟩

end GradientHessian.NumericalCachedEarlyPhase
