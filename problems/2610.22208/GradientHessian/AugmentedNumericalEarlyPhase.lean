import GradientHessian.AugmentedNumericalEquality
import GradientHessian.AugmentedNumericalCaches
import GradientHessian.AugmentedEarlyPhase
import GradientHessian.ControllerGuardedReverse

/-! Every early numerical point of the full augmented policy occurs in the
actual cached run before target feedback. Initialization reads the complete
source packet, reconstructed from the supplied target and charged prior cache. -/

noncomputable section
namespace GradientHessian.AugmentedNumericalEarlyPhase
open Classical HigherHierarchy HierarchyAddresses RawHierarchy FrontierState TaskState TaskSlots
  GeometricRepair ComparisonController ComparisonControllerReplay ControllerPolicyDriver
  ControllerNormalRealization ControllerDriverMonotonicity NumericalCachedOracle
  NumericalCoefficientPatch NumericalShadowRules VisibilityWindow VisibilityTaskWindow

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable [∀ t,MeasurableSpace (DirectionPolicyReplay.Point d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Rich d J E H t)]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (leaf : Leaf (t+1))
variable [BorelSpace (DirectionPolicyReplay.Point d J E H t)]
  [BorelSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [BorelSpace (DirectionPolicyReplay.Rich d J E H t)]
variable (policy : Machine.Policy (Seed × AugmentedPolicy.Packet d J E H t ell) S
  (DirectionPolicyReplay.Point d J E H t)
  (AugmentedPolicy.Ordinary d J E H t ell) (AugmentedPolicy.Rich d J E H t ell))

theorem early_phase {K : ℝ} (hK : 0<K) (hell : 0<ell)
    (x : Raw d n r J E H t × Seed) (c : Cache d J) (j : Fin (4096*J^2+1))
    (hb : ∀ k,k≤j → c.1 k=(atLeaf t ((leafEquiv t).symm leaf) (coefficients P B fallback t x.1)).2.1 k)
    (ha : ∀ k,k<j → c.2 k=(atLeaf t ((leafEquiv t).symm leaf) (coefficients P B fallback t x.1)).2.2.1 k)
    (hz : c.2 j=0) (N : ℕ)
    (he : x∈AugmentedEarlyPhase.earlyEvent P B fallback t policy K N leaf j) :
    ∃ i<(N+1)*(8^(t+1)+4),∃ rem a output p s,
      ControllerPolicyDriver.run policy
        (shadowRules P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x.1).2 c)
        (fun _ => false)
        (AugmentedNumericalEquality.ordinary P B fallback t leaf K
          (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x.1).2 c
          (MatrixGoodSpectrum.sourceMatrix P J (RawLeafFactor.leafNumerical t x.1 ((leafEquiv t).symm leaf)).1))
        (AugmentedNumericalReplies.rich P B fallback t leaf K
          (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x.1).2 c)
        i (AugmentedNumericalDriver.startConfig t P B fallback leaf policy K N x.2
          (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x.1).2 c)=
          .pending rem a output (.normal p s) ∧
      IsEarlyFor (rules K (assemble P B fallback t x.1)) p s (leaf,j) ∧ taskDisclosed leaf j s=false := by
  obtain ⟨i,hi,rem,a,output,p,s,hm,hearly,hstop⟩ :=
    AugmentedEarlyPhase.masked_normal_phase P B fallback t policy K hell N x leaf j he
  let R : Rules (t+1) (4096*J^2+1) ell (DirectionPolicyReplay.Point d J E H t) (Action t (4096*J^2)) := ControllerHitMasking.mask
    (suppress (rules K (assemble P B fallback t x.1)) (blockLeaf leaf)) (GeometricMaskedEarly.targetTask leaf j)
  have hretire : ∀ u : State (t+1) (4096*J^2+1) ell,Ready u → ∀ act : Action t (4096*J^2),
      taskDisclosed leaf j u=true → taskDisclosed leaf j (retireNode u (target act))=true := by
    intro u _ act hu
    exact taskDisclosed_completed_mono leaf j u _ (retireSet_completed_mono u _) hu
  have hnormal : ∀ u : State (t+1) (4096*J^2+1) ell,Ready u → ∀ p,
      taskDisclosed leaf j u=true → taskDisclosed leaf j (normal R p u)=true := by
    intro u hu p hs
    exact taskDisclosed_completed_mono leaf j u _ (normal_completed_mono R p hu) hs
  have hguard := guarded_eq_at_open_endpoint policy R (taskDisclosed leaf j)
    (AugmentedPolicy.ordinary P B fallback K t x.1) (AugmentedPolicy.rich P B fallback K t x.1)
    hell hretire hnormal (AugmentedPolicy.initial P B fallback t policy K x.1 N x.2 TaskState.initial)
    (initial_ready hell) i (by change taskDisclosed leaf j (stateOf _) = false; rw [hm]; exact hstop)
  have hg := hguard.trans hm
  have hc := AugmentedNumericalEquality.run_eq P B fallback t leaf policy hK x.1 c j hb ha hz i
    (AugmentedPolicy.initial P B fallback t policy K x.1 N x.2 TaskState.initial) (by trivial)
  have heq := hc.trans hg
  have hrev := ControllerGuardedReverse.run_eq_of_open_endpoint policy
    (shadowRules P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x.1).2 c)
    (taskDisclosed leaf j)
    (AugmentedNumericalEquality.ordinary P B fallback t leaf K
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x.1).2 c
      (MatrixGoodSpectrum.sourceMatrix P J (RawLeafFactor.leafNumerical t x.1 ((leafEquiv t).symm leaf)).1))
    (AugmentedNumericalReplies.rich P B fallback t leaf K
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x.1).2 c)
    i (AugmentedPolicy.initial P B fallback t policy K x.1 N x.2 TaskState.initial) (by trivial)
    (by rw [heq]; exact hstop)
  have hinit : AugmentedNumericalDriver.startConfig t P B fallback leaf policy K N x.2
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x.1).2 c=
        AugmentedPolicy.initial P B fallback t policy K x.1 N x.2 TaskState.initial :=
    AugmentedNumericalDriver.initialize_after_supply t P B fallback leaf policy K N x.2 x.1 c j hb ha
  refine ⟨i,hi,rem,a,output,p,s,?_,hearly,hstop⟩
  rw [hinit]
  exact hrev.symm.trans heq

end GradientHessian.AugmentedNumericalEarlyPhase
