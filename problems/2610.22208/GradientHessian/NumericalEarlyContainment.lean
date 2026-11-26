import GradientHessian.NumericalCompiledEndpoint
import GradientHessian.NumericalSavedConfiguration
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
namespace GradientHessian.NumericalEarlyContainment
open Matrix
open scoped InnerProductSpace
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

theorem early_mem_rawEvent {K : ℝ} (hK : 0<K) (hell : 0<ell)
    (x : RawHierarchy.Raw d n r J E H t × Seed)
    (hd : Valid _ _ _ _ t (RawHierarchy.assemble P B fallback t x.1))
    (N : ℕ) (j : Fin (4096*J^2+1))
    (he : x∈NumericalEarlyExpectation.earlyEvent (ell := ell) P B fallback t leaf policy K N j) :
    x∈NumericalForkProbability.rawEvent (ell := ell) P B fallback t leaf policy hK j N := by
  let w := input t leaf j x
  let A := ForkMachineBound.sourceA J P w
  let readout := ForkMachineBound.earlierReadout J P fallback w
  let c := postCache P B fallback t leaf j x
  let R := NumericalShadowRules.shadowRules (ell := ell) P B fallback t leaf K w.1.2.2.1 c
  let o := NumericalProductStep.ordinary (ell := ell) P B fallback t leaf K w.1.2.2.1 c A
  let v := NumericalPolicyReplies.rich (ell := ell) P B fallback t leaf K w.1.2.2.1 c
  let q0 : Config (t+1) (4096*J^2+1) ell S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
      (Action t (4096*J^2)) := ControllerPolicyDriver.initial policy N x.2 TaskState.initial
  have hA : A=MatrixGoodSpectrum.sourceMatrix P J (RawLeafFactor.leafNumerical t x.1 ((leafEquiv t).symm leaf)).1 :=
    matrix_eq P t leaf j x
  have hrest : w.1.2.2.1=(RawLeafFactor.factor t ((leafEquiv t).symm leaf) x.1).2 := external_eq t leaf j x
  have hseed : w.1.2.2.2=x.2 := seed_eq t leaf j x
  obtain ⟨i,hi,rem,a,output,p,u,hrun,hearly,hstop⟩ :=
    NumericalCachedEarlyPhase.early_phase P B fallback t leaf policy hK hell x.1 hd c j
      (fun k _ => congrFun (post_forcing P B fallback t leaf j x) k)
      (fun k hk => post_readout P B fallback t leaf j k x hk)
      (post_zero P B fallback t leaf j x) N x.2 he
  have hu : ControllerPolicyDriver.run policy R (fun _ => false) o v i q0=.pending rem a output (.normal p u) := by
    simpa only [R,o,v,A,c,q0,hA,hrest] using hrun
  have hfinished : NumericalDriverInstructions.finished (ControllerPolicyDriver.run policy R (fun _ => false) o v i q0)=false := by
    rw [hu]
    rfl
  obtain ⟨k,hki,hpre,hkfinished,hkcurrent,hkindex,hkexternal,hkresidual⟩ :=
    NumericalSupplySplit.split_at_supply policy R o v hell q0 (initial_ready hell) leaf j i hfinished
      (by rw [hu]; exact hearly.1) (by rw [hu]; exact hearly.2.1)
  let saved := NumericalPreloadTransparency.savedRuntime (ell := ell) P B fallback t leaf policy K j A readout N w.1.2 k
  have hsaved : saved.2.2=ControllerPolicyDriver.run policy R (fun _ => false) o v k q0 := by
    have hsaved0 := NumericalSavedConfiguration.saved_config P B fallback t leaf policy hK hell x N k j
    change saved.2.2=_ at hsaved0
    change (NumericalPreloadExecution.externalStep P B fallback t leaf policy K j w.1.2.2.1 c A)^[k] q0=_ at hkexternal
    rw [hrest,hA] at hkexternal
    exact hsaved0.trans hkexternal
  have hsready : Ready (stateOf saved.2.2) := by
    rw [hsaved]
    exact run_good policy R (fun _ => false) o v hell q0 (initial_ready hell) k
  have hscurrent : TaskState.current (stateOf saved.2.2)=some leaf := by rw [hsaved]; exact hkcurrent
  have hsindex : ((stateOf saved.2.2).completed leaf).val=j.val := by rw [hsaved]; exact hkindex
  have hsfinished : NumericalDriverInstructions.finished saved.2.2=false := by rw [hsaved]; exact hkfinished
  let branch := NumericalPostprocessor.initial t saved w.2.1
  have hbranchcache : NumericalPostprocessor.cache B t j branch=c :=
    post_saved_cache P B fallback t leaf policy K j N k x
  have hnormal : ∀ s : State (t+1) (4096*J^2+1) ell,Ready s → ∀ p',
      taskDisclosed leaf j s=true → taskDisclosed leaf j (normal R p' s)=true := by
    intro s hs p' hh
    apply decide_eq_true
    exact (of_decide_eq_true hh).trans_le (normal_completed_mono R p' hs leaf)
  have hscoherent : Coherent (taskDisclosed leaf j) saved.2.2 := by
    rw [hsaved]
    exact run_coherent policy R (taskDisclosed leaf j) o v hell hnormal q0 (initial_ready hell) k
  have hres : NumericalPostEndpoint.unguarded P B fallback t leaf policy K j A branch (i-k)=
      .pending rem a output (.normal p u) := by
    change ControllerPolicyDriver.run policy
      (NumericalShadowRules.shadowRules P B fallback t leaf K w.1.2.2.1 (NumericalPostprocessor.cache B t j branch))
      (fun _ => false)
      (NumericalProductStep.ordinary P B fallback t leaf K w.1.2.2.1 (NumericalPostprocessor.cache B t j branch) A)
      (NumericalPolicyReplies.rich P B fallback t leaf K w.1.2.2.1 (NumericalPostprocessor.cache B t j branch))
      (i-k) saved.2.2=_
    rw [hbranchcache,hsaved]
    exact hkresidual.trans hu
  exact NumericalCompiledEndpoint.rawEvent_of_endpoint P B fallback t leaf policy hK hell x N j
    k (i-k) rem a output p u hsready hscoherent hscurrent hsindex hsfinished hres hearly hstop

end GradientHessian.NumericalEarlyContainment
