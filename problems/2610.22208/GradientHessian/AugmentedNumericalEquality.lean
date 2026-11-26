import GradientHessian.AugmentedNumericalRuntime
import GradientHessian.NumericalMaskedDriverEquality
import GradientHessian.ControllerExternalReceiptCongruence
noncomputable section
namespace GradientHessian.AugmentedNumericalEquality
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
variable (policy : Machine.Policy (Seed × AugmentedPolicy.Packet d J E H t ell) S
  (DirectionPolicyReplay.Point d J E H t)
  (AugmentedPolicy.Ordinary d J E H t ell) (AugmentedPolicy.Rich d J E H t ell))
def ordinary (K : ℝ) (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J)
    (A : Matrix (Fin d) (Fin d) ℝ) (before after : State (t+1) (4096*J^2+1) ell)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :=
  AugmentedNumericalReplies.ordinary P B fallback t leaf K w c before after Z
    (LowRank.matrixEuclideanMap A (CensoredOracle.numericalMap t Z))

def fullStep (K : ℝ) (stop : State (t+1) (4096*J^2+1) ell → Bool)
    (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J) (A : Matrix (Fin d) (Fin d) ℝ)
    (q : Config (t+1) (4096*J^2+1) ell S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
      (Action t (4096*J^2))) :=
  ControllerPolicyDriver.step policy (NumericalShadowRules.shadowRules P B fallback t leaf K w c) stop
    (ordinary P B fallback t leaf K w c A) (AugmentedNumericalReplies.rich P B fallback t leaf K w c) q

theorem product_coordinates (A : Matrix (Fin d) (Fin d) ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    (NumericalOrdinaryProcedure.coordinates d).symm (A *ᵥ (NumericalOrdinaryProcedure.coordinates d y))=
      LowRank.matrixEuclideanMap A y := rfl

theorem one_product_step (K : ℝ) (stop : State (t+1) (4096*J^2+1) ell → Bool)
    (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J) (A : Matrix (Fin d) (Fin d) ℝ)
    (q : Config (t+1) (4096*J^2+1) ell S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
      (Action t (4096*J^2))) :
    AugmentedNumericalRuntime.advance P B fallback t leaf policy K stop w c
      (if NumericalDriverInstructions.product leaf stop q then
        LowRank.matrixEuclideanMap A (CensoredOracle.numericalMap t (NumericalDriverInstructions.point q)) else 0) q=
      fullStep P B fallback t leaf policy K stop w c A q := by
  cases q with
  | ready N a s => rfl
  | finished a s => rfl
  | pending N a output phase =>
      cases phase with
      | repairing p s => rfl
      | normal p s => rfl
      | frozen p s => rfl
      | delivered p before after =>
          cases hb : stop before <;> cases ha : stop after
          all_goals simp only [AugmentedNumericalRuntime.advance,fullStep,ControllerPolicyDriver.step,
            ControllerPolicyDriver.deliver,hb,ha,Bool.or_false,Bool.or_true,if_true,
            Bool.false_eq_true,if_false]
          cases output with
          | true => rfl
          | false =>
              cases hp : p.kind with
              | rich => simp only [hp]
              | ordinary =>
                  by_cases hc : TaskState.current before=some leaf
                  · simp [ordinary,hp,AugmentedNumericalReplies.ordinary,NumericalPolicyReplies.ordinary,hc,NumericalDriverInstructions.product,
                      NumericalDriverInstructions.point,phaseEquiv,hb,ha]
                  · simp [ordinary,hp,AugmentedNumericalReplies.ordinary,NumericalPolicyReplies.ordinary,hc]

open NumericalCoefficientPatch CensoredOracle NumericalShadowRules GeometricMaskedEarly

theorem ordinary_open {K : ℝ} (hK : 0<K)
    (x : RawHierarchy.Raw d n r J E H t) (c : Cache d J) (j : Fin (4096*J^2+1))
    (hb : ∀ k,k≤j → c.1 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.1 k)
    (ha : ∀ k,k<j → c.2 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.2.1 k)
    (before after : State (t+1) (4096*J^2+1) ell)
    (hsb : taskDisclosed leaf j before=false) (hsa : taskDisclosed leaf j after=false)
    (Z : DirectionPolicyReplay.Point d J E H t) :
    ordinary P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c
      (MatrixGoodSpectrum.sourceMatrix P J (RawLeafFactor.leafNumerical t x ((leafEquiv t).symm leaf)).1)
      before after Z=AugmentedPolicy.ordinary P B fallback K t x before after Z := by
  apply Prod.ext
  · change (if _ then _ else _) = DirectionPolicy.ordinary _ _ _ _ _ _
    rw [AugmentedNumericalReplies.ordinary_guard P B fallback t leaf K x before after j hsa]
    split_ifs
    · exact NumericalMaskedDriverEquality.ordinary_open P B fallback t leaf hK x c j hb ha before after hsb hsa Z
    · rfl
  · exact AugmentedNumericalPacket.packet_before_disclosure P B fallback t leaf K x c j after hsa hb ha

theorem run_eq {K : ℝ} (hK : 0<K)
    (x : RawHierarchy.Raw d n r J E H t) (c : Cache d J) (j : Fin (4096*J^2+1))
    (hb : ∀ k,k≤j → c.1 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.1 k)
    (ha : ∀ k,k<j → c.2 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.2.1 k)
    (hz : c.2 j=0) (N : ℕ)
    (q : Config (t+1) (4096*J^2+1) ell S (DirectionPolicyReplay.Point d J E H t) (Action t (4096*J^2)))
    (hq : ControllerReceiptCongruence.Receipt
      (shadowRules P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c) q) :
    ControllerPolicyDriver.run policy
      (shadowRules P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c)
      (taskDisclosed leaf j)
      (ordinary P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c
        (MatrixGoodSpectrum.sourceMatrix P J (RawLeafFactor.leafNumerical t x ((leafEquiv t).symm leaf)).1))
      (AugmentedNumericalReplies.rich P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c) N q =
    ControllerPolicyDriver.run policy
      (ControllerHitMasking.mask (suppress (rules K (RawHierarchy.assemble P B fallback t x)) (blockLeaf leaf)) (targetTask leaf j))
      (taskDisclosed leaf j) (AugmentedPolicy.ordinary P B fallback K t x) (AugmentedPolicy.rich P B fallback K t x) N q := by
  have hread := NumericalMaskedDriverEquality.cached_readouts P B fallback t leaf x c j ha
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
    exact AugmentedNumericalReplies.rich_before_disclosure P B fallback t leaf hK x c j hb ha
      _ p hk before after he hsa
  · exact hq

theorem external_eq_source {K : ℝ} (hK : 0<K) (hell : 0<ell)
    (x : RawHierarchy.Raw d n r J E H t) (c : Cache d J) (j : Fin (4096*J^2+1))
    (hb : ∀ k,k<j → c.1 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.1 k)
    (ha : ∀ k,k<j → c.2 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.2.1 k)
    (N : ℕ)
    (q : Config (t+1) (4096*J^2+1) ell S (DirectionPolicyReplay.Point d J E H t) (Action t (4096*J^2)))
    (hc : ControllerDriverMonotonicity.Coherent (AugmentedDisclosure.markStop leaf j) q)
    (hq : ControllerReceiptCongruence.Receipt
      (shadowRules P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c) q) :
    (ControllerExternalReceiptCongruence.external policy
      (shadowRules P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c)
      (AugmentedDisclosure.markStop leaf j) NumericalDriverInstructions.finished
      (ordinary P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c
        (MatrixGoodSpectrum.sourceMatrix P J (RawLeafFactor.leafNumerical t x ((leafEquiv t).symm leaf)).1))
      (AugmentedNumericalReplies.rich P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c))^[N] q =
    (ControllerExternalReceiptCongruence.external policy
      (suppress (rules K (RawHierarchy.assemble P B fallback t x)) (blockLeaf leaf))
      (AugmentedDisclosure.markStop leaf j) NumericalDriverInstructions.finished
      (AugmentedPolicy.ordinary P B fallback K t x) (AugmentedPolicy.rich P B fallback K t x))^[N] q := by
  have hread := NumericalMaskedDriverEquality.cached_readouts P B fallback t leaf x c j ha
  apply ControllerExternalReceiptCongruence.external_iterate_congr policy
  · rfl
  · rfl
  · intro s hs Z a
    exact (NumericalRuleAgreement.pre_rules P B fallback t leaf K x c j hread s
      (AugmentedDisclosure.markStop_open leaf j s hs) Z).2.2.1 a
  · intro s hs Z
    exact (NumericalRuleAgreement.pre_rules P B fallback t leaf K x c j hread s
      (AugmentedDisclosure.markStop_open leaf j s hs) Z).2.2.2
  · intro before after hsb hsa Z
    have he := AugmentedNumericalReplies.ordinary_before_supply P B fallback t leaf hK x c j hb ha
      before after hsb hsa Z
    rw [NumericalPriorCache.coefficient_A] at he
    exact he
  · intro p before after hk he _ hsa
    exact AugmentedNumericalReplies.rich_before_supply P B fallback t leaf hK x c j hb ha
      _ p hk before after he hsa
  · exact hell
  · intro s hs p hstop
    exact AugmentedDisclosure.markStop_normal_mono leaf j _ p s hs hstop
  · exact hc
  · exact hq

end GradientHessian.AugmentedNumericalEquality

