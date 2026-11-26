import GradientHessian.NumericalRuleAgreement
import GradientHessian.NumericalRichAgreement
import GradientHessian.ControllerReceiptCongruence
import GradientHessian.NumericalProductStep
import GradientHessian.NumericalRuntime
import GradientHessian.NumericalOrdinaryProcedure
noncomputable section
namespace GradientHessian.NumericalMaskedDriverEquality
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

theorem ordinary_open {K : ℝ} (hK : 0<K)
    (x : RawHierarchy.Raw d n r J E H t) (c : Cache d J) (j : Fin (4096*J^2+1))
    (hb : ∀ k,k≤j → c.1 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.1 k)
    (ha : ∀ k,k<j → c.2 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.2.1 k)
    (before after : State (t+1) (4096*J^2+1) ell)
    (hsb : taskDisclosed leaf j before=false) (hsa : taskDisclosed leaf j after=false)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    NumericalProductStep.ordinary P B fallback t leaf K
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c
      (MatrixGoodSpectrum.sourceMatrix P J (RawLeafFactor.leafNumerical t x ((leafEquiv t).symm leaf)).1)
      before after Z = CensoredPolicy.ordinaryReply K t (RawHierarchy.coefficients P B fallback t x) before after Z := by
  have he : NumericalPolicyReplies.ordinary P B fallback t leaf K
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c before after Z
      ((atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).1 (numericalMap t Z))=
      CensoredPolicy.ordinaryReply K t (RawHierarchy.coefficients P B fallback t x) before after Z := by
    cases hs : markSupplied leaf j before with
    | false =>
        exact NumericalCacheReplyAgreement.ordinary_before_supply P B fallback t leaf hK x c j
          (fun k hk => hb k hk.le) ha before after hs Z
    | true =>
        have hd := of_decide_eq_false hsb
        change ¬j.val<(before.completed leaf).val at hd
        obtain hh | ⟨hc,hj⟩ := of_decide_eq_true hs
        · have hh' := (TaskState.mem_retired before leaf).mp hh
          have ht : j.val<(before.completed leaf).val := by simpa only [hh'] using j.isLt
          exact False.elim (hd ht)
        · have hj' : (before.completed leaf).val=j.val := by omega
          exact NumericalCacheReplyAgreement.ordinary_after_supply P B fallback t leaf hK x c j hb ha
            before after hc hj' hsa Z
  rw [NumericalPriorCache.coefficient_A] at he
  exact he

theorem cached_readouts (x : RawHierarchy.Raw d n r J E H t) (c : Cache d J)
    (j : Fin (4096*J^2+1))
    (ha : ∀ k,k<j → c.2 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.2.1 k) :
    ∀ k,k<j → c.2 k=(leafCoefficients (RawHierarchy.assemble P B fallback t x) leaf).a k := by
  intro k hk
  rw [ha k hk,NumericalPriorCache.coefficient_a]
  change _=(leafData t (RawHierarchy.assemble P B fallback t x) ((leafEquiv t).symm leaf)).a k
  rw [RawLeafFactor.leaf_a_assemble]
  rfl

theorem run_eq {K : ℝ} (hK : 0<K)
    (x : RawHierarchy.Raw d n r J E H t) (c : Cache d J) (j : Fin (4096*J^2+1))
    (hb : ∀ k,k≤j → c.1 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.1 k)
    (ha : ∀ k,k<j → c.2 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.2.1 k)
    (hz : c.2 j=0) (N : ℕ)
    (q : Config (t+1) (4096*J^2+1) ell S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
      (Action t (4096*J^2)))
    (hq : ControllerReceiptCongruence.Receipt
      (shadowRules P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c) q) :
    ControllerPolicyDriver.run policy
      (shadowRules P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c)
      (taskDisclosed leaf j)
      (NumericalProductStep.ordinary P B fallback t leaf K
        (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c
        (MatrixGoodSpectrum.sourceMatrix P J (RawLeafFactor.leafNumerical t x ((leafEquiv t).symm leaf)).1))
      (NumericalPolicyReplies.rich P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c) N q =
    ControllerPolicyDriver.run policy
      (ControllerHitMasking.mask (suppress (rules K (RawHierarchy.assemble P B fallback t x)) (blockLeaf leaf)) (targetTask leaf j))
      (taskDisclosed leaf j)
      (CensoredPolicy.ordinaryReply K t (RawHierarchy.coefficients P B fallback t x))
      (CensoredPolicy.richReply K t (RawHierarchy.coefficients P B fallback t x)) N q := by
  have hread := cached_readouts P B fallback t leaf x c j ha
  apply ControllerReceiptCongruence.run_congr policy
  · rfl
  · rfl
  · intro s hs Z a
    exact (NumericalRuleAgreement.post_rules P B fallback t leaf K x c j hread hz s hs Z).2.2.1 a
  · intro s hs Z
    exact (NumericalRuleAgreement.post_rules P B fallback t leaf K x c j hread hz s hs Z).2.2.2
  · intro before after hsb hsa Z
    exact ordinary_open P B fallback t leaf hK x c j hb ha before after hsb hsa Z
  · intro p before after hk he _ hsa
    exact NumericalRichAgreement.rich_after_supply P B fallback t leaf hK x c j _ p hk before after he hsa
  · exact hq

end GradientHessian.NumericalMaskedDriverEquality
