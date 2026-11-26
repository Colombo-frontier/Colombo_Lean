import GradientHessian.GeometricStoppedAction
import GradientHessian.DirectionPolicyReplies
import GradientHessian.DirectionFactorActions

/-! Original true-jet repair events reach a blocked hit in the actual
direction-censored driver. Receipt correctness and disclosure persistence
are discharged for the literal controller, including the virtual output. -/

noncomputable section
namespace GradientHessian.DirectionStoppedAction
universe u
open Classical HigherHierarchy HierarchyParameters CensoredOracle ControllerCensor
  FrontierState TaskState TaskSlots ComparisonController GeometricDisclosure GeometricRepair JetLocality
  CensoredPolicy ControllerPolicyDriver ComparisonControllerReplay ControllerRepairEvents

variable {Y E : Type u} {H : ℕ → Type u} {m ell : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (t : ℕ)
variable [MeasurableSpace (Space Y E H m t)]
  [MeasurableSpace (ℝ × (Space Y E H m t →L[ℝ] ℝ))]
  [MeasurableSpace (ℝ × (Space Y E H m t →L[ℝ] ℝ) ×
    (Space Y E H m t →L[ℝ] Space Y E H m t →L[ℝ] ℝ))]
variable (P : Machine.Policy Seed S (Space Y E H m t)
  (ℝ × (Space Y E H m t →L[ℝ] ℝ))
  (ℝ × (Space Y E H m t →L[ℝ] ℝ) × (Space Y E H m t →L[ℝ] Space Y E H m t →L[ℝ] ℝ)))

theorem original_action_has_shadow_hit {K : ℝ} (hK : 0<K) (θ : Parameters Y E H m t)
    (hd : Valid Y E H m t (decode t θ)) (hell : 0<ell) (N : ℕ) (seed : Seed)
    (a : Action t m) (blocked : Action t m → Bool) (hb : blocked a=true)
    (ha : a ∈ actions (rules (ell := ell) K (decode t θ))
      (ControllerPolicyTrace.withOutput P (ordinaryJet (scalar K t (decode t θ)))
        (richJet (scalar K t (decode t θ))) N seed) TaskState.initial) :
    ∃ j<(N+1)*(8^(t+1)+4), ControllerPolicyCoupling.BlockedHit (rules (ell := ell) K (decode t θ)) blocked (actionStop a)
      (run P (suppress (rules K (decode t θ)) blocked) (actionStop a)
        (DirectionPolicy.ordinary K t θ) (DirectionPolicy.rich K t θ) j
        (ControllerPolicyDriver.initial P N seed TaskState.initial)) := by
  apply ControllerStoppedAction.original_action_has_shadow_hit P (rules K (decode t θ))
    (ordinaryJet (scalar K t (decode t θ))) (richJet (scalar K t (decode t θ)))
    (DirectionPolicy.ordinary K t θ) (DirectionPolicy.rich K t θ)
    (fun s => Ready s ∧ LastChildClosed (TaskState.retired s))
    (fun _ hs => hs.1) _ _ _ a blocked hb (actionStop a) _ _ _ hell N seed TaskState.initial _ ha
  · intro s hs p
    exact ⟨serve_ready _ p hs.1 hell,(serve_lastChildClosed K (decode t θ) p s hs.2).2⟩
  · intro s hs p
    rw [DirectionPolicy.ordinary_receipt K t θ _ p s hs.1]
    apply serve_completedOrdinary hK t θ s p hs.1 hs.2
    intro leaf
    exact (leafData_valid t (decode t θ) hd ((HierarchyAddresses.leafEquiv t).symm leaf)).2.2.1
  · intro s hs p
    rw [DirectionPolicy.rich_receipt K t θ _ p s hs.1]
    exact serve_completedRich hK t θ s p hs.1 hs.2
  · intro s _ b hs
    exact actionStop_retireNode_mono a s (target b) hs
  · intro s hs p hstop
    exact actionStop_normal_mono a (rules K (decode t θ)) p s hs hstop
  · intro p s hc
    exact chosen_actionStop_false K (decode t θ) s p a hc
  · exact ⟨initial_ready hell,initial_lastChildClosed (by omega)⟩

end GradientHessian.DirectionStoppedAction
