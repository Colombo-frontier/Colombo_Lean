import GradientHessian.AugmentedNumericalCompiledEndpoint
import GradientHessian.AugmentedNumericalSavedConfiguration
import GradientHessian.AugmentedNumericalSupplySplit
import GradientHessian.AugmentedNumericalEarlyPhase
import GradientHessian.AugmentedNumericalCursorInvariant

noncomputable section
namespace GradientHessian.AugmentedNumericalEarlyContainment
open Classical Matrix HigherHierarchy HierarchyAddresses RawHierarchy FrontierState TaskState TaskSlots
  ComparisonController ComparisonControllerReplay GeometricRepair ControllerNormalRealization
  NumericalSourceCaches ControllerPolicyDriver ControllerDriverMonotonicity VisibilityTaskWindow

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

theorem early_mem_rawEvent {K : ℝ} (hK : 0<K) (hell : 0<ell)
    (x : Raw d n r J E H t × Seed) (N : ℕ) (j : Fin (4096*J^2+1))
    (he : x∈AugmentedEarlyPhase.earlyEvent P B fallback t policy K N leaf j) :
    x∈AugmentedNumericalProbability.rawEvent P B fallback t leaf policy hK j N := by
  let w := input t leaf j x
  let A := ForkMachineBound.sourceA J P w
  let readout := ForkMachineBound.earlierReadout J P fallback w
  let c := postCache P B fallback t leaf j x
  let R := NumericalShadowRules.shadowRules (ell := ell) P B fallback t leaf K w.1.2.2.1 c
  let o := AugmentedNumericalEquality.ordinary (ell := ell) P B fallback t leaf K w.1.2.2.1 c A
  let v := AugmentedNumericalReplies.rich (ell := ell) P B fallback t leaf K w.1.2.2.1 c
  let q0 := AugmentedNumericalDriver.startConfig t P B fallback leaf policy K N w.1.2.2.2 w.1.2.2.1 c
  let z : AugmentedNumericalDriver.Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t :=
    Sum.inl PUnit.unit.{2}
  have hstate (q : AugmentedNumericalDriver.Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t) :
      AugmentedNumericalCursorCounts.state q0 q=AugmentedNumericalDriver.state t q := by cases q <;> rfl
  have hfinished (q : AugmentedNumericalDriver.Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t) :
      AugmentedNumericalSupplySplit.finished q=AugmentedNumericalDriver.finished t q := by cases q <;> rfl
  have hA : A=MatrixGoodSpectrum.sourceMatrix P J (RawLeafFactor.leafNumerical t x.1 ((leafEquiv t).symm leaf)).1 :=
    matrix_eq P t leaf j x
  have hrest : w.1.2.2.1=(RawLeafFactor.factor t ((leafEquiv t).symm leaf) x.1).2 := external_eq t leaf j x
  have hseed : w.1.2.2.2=x.2 := seed_eq t leaf j x
  obtain ⟨i,hi,rem,a,output,p,u,hrun,hearly,hstop⟩ :=
    AugmentedNumericalEarlyPhase.early_phase P B fallback t leaf policy hK hell x c j
      (fun k _ => congrFun (post_forcing P B fallback t leaf j x) k)
      (fun k hk => post_readout P B fallback t leaf j k x hk)
      (post_zero P B fallback t leaf j x) N he
  have hurun : ControllerPolicyDriver.run policy R (fun _ => false) o v i q0=.pending rem a output (.normal p u) := by
    simpa only [R,o,v,A,c,q0,hA,hrest,hseed] using hrun
  have hu : AugmentedNumericalCursorCounts.run policy R (fun _ => false) o v q0 (i+1) z=
      Sum.inr (.pending rem a output (.normal p u)) := by
    rw [AugmentedNumericalCursorCounts.run_suspended_succ,hurun]
  obtain ⟨k,hki,hpre,hkfinished,hkcurrent,hkindex,hkexternal,hkresidual,hkafter⟩ :=
    AugmentedNumericalSupplySplit.split_at_supply policy R o v q0 hell z (initial_ready hell) leaf j (i+1)
      (by rw [hu]; rfl) (by rw [hu]; exact hearly.1) (by rw [hu]; exact hearly.2.1)
  let saved := AugmentedNumericalPreTransparency.savedRuntime.{_,_,1} P B fallback t leaf policy K j A readout N w.1.2 k
  have hsaved : saved.2.2=AugmentedNumericalCursorCounts.run policy R (fun _ => false) o v q0 k z := by
    have hsaved0 := AugmentedNumericalSavedConfiguration.saved_config P B fallback t leaf policy hK hell x N k j
    change saved.2.2=_ at hsaved0
    have hext : AugmentedNumericalSupplyEquality.externalCursor P B fallback t leaf policy K N j
        w.1.2.2.2 w.1.2.2.1 c A=
        ExternalHaltIteration.step (AugmentedNumericalCursorCounts.step policy R (fun _ => false) o v q0)
          (AugmentedNumericalSupplySplit.halt q0 leaf j) := by
      funext q
      unfold AugmentedNumericalSupplyEquality.externalCursor ExternalHaltIteration.step AugmentedNumericalSupplySplit.halt
      rw [hstate,hfinished]
      rfl
    rw [hext] at hsaved0
    exact hsaved0.trans hkexternal
  have hsready : Ready (AugmentedNumericalDriver.state t saved.2.2) := by
    rw [← hstate]
    rw [hsaved]
    exact AugmentedNumericalCursorInvariant.run_ready policy R o v q0 (fun _ => false) hell k z (initial_ready hell)
  have hscurrent : TaskState.current (AugmentedNumericalDriver.state t saved.2.2)=some leaf := by
    rw [hsaved]
    simpa only [hstate] using hkcurrent
  have hsindex : ((AugmentedNumericalDriver.state t saved.2.2).completed leaf).val=j.val := by
    rw [hsaved]
    simpa only [hstate] using hkindex
  have hsfinished : AugmentedNumericalDriver.finished t saved.2.2=false := by
    rw [hsaved]
    simpa only [hfinished] using hkfinished
  have hnormal : ∀ s : State (t+1) (4096*J^2+1) ell,Ready s → ∀ p',
      taskDisclosed leaf j s=true → taskDisclosed leaf j (normal R p' s)=true := by
    intro s hs p' hh
    apply decide_eq_true
    exact (of_decide_eq_true hh).trans_le (normal_completed_mono R p' hs leaf)
  have hscoherent : AugmentedNumericalCursorInvariant.coherent (taskDisclosed leaf j) saved.2.2 := by
    rw [hsaved]
    exact AugmentedNumericalCursorInvariant.run_coherent policy R o v q0 (taskDisclosed leaf j)
      hell hnormal (initial_ready hell) k z (by intro q hq; dsimp only [z] at hq; cases hq)
  let branch := AugmentedNumericalPostprocessor.initial t saved w.2.1
  have hbranchcache : AugmentedNumericalPostprocessor.cache t B j branch=c :=
    AugmentedNumericalSavedConfiguration.post_saved_cache P B fallback t leaf policy K x N k j
  have hres : AugmentedNumericalPostEndpoint.unguarded t P B fallback leaf policy K N j A branch (i+1-k)=
      Sum.inr (.pending rem a output (.normal p u)) := by
    change (AugmentedNumericalExecution.fullCursor P B fallback t leaf policy K N (fun _ => false)
      w.1.2.2.2 w.1.2.2.1 (AugmentedNumericalPostprocessor.cache t B j branch) A)^[i+1-k] saved.2.2=_
    rw [hbranchcache,hsaved]
    exact hkresidual.trans hu
  exact AugmentedNumericalCompiledEndpoint.rawEvent_of_endpoint P B fallback t leaf policy hK hell x N j
    k (i+1-k) rem a output p u hsready hscoherent hscurrent hsindex hsfinished hres hearly hstop

end GradientHessian.AugmentedNumericalEarlyContainment
