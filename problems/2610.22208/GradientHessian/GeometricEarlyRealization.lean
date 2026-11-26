import GradientHessian.ControllerEarlyRealization
import GradientHessian.CensoredOriginalExecution

/-! The actual true-jet early event has a concrete pre-feedback normal
phase. Geometric validity discharges all policy execution premises. -/

noncomputable section
namespace GradientHessian.GeometricEarlyRealization
universe u
open Classical HigherHierarchy HierarchyParameters CensoredOracle ControllerCensor
  FrontierState TaskState TaskSlots ComparisonController GeometricRepair JetLocality
  CensoredPolicy ControllerPolicyDriver ControllerNormalRealization GeometricDisclosure

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

theorem original_early_has_normal_phase {K : ℝ} (hK : 0<K) (θ : Parameters Y E H m t)
    (hd : Valid Y E H m t (decode t θ)) (hell : 0<ell) (N : ℕ) (seed : Seed)
    (leaf : Leaf (t+1)) (j : Fin (m+1))
    (he : 0<ControllerEarlyEvents.count (rules (ell := ell) K (decode t θ))
      (ControllerPolicyTrace.withOutput P (ordinaryJet (scalar K t (decode t θ)))
        (richJet (scalar K t (decode t θ))) N seed) TaskState.initial (leaf,j)) :
    ∃ i<(N+1)*(8^(t+1)+4), ∃ n b output p s,
      run P (rules (ell := ell) K (decode t θ)) (fun _ => false)
        (completedOrdinary K t θ) (completedRich K t θ) i
        (ControllerPolicyDriver.initial P N seed TaskState.initial)=
        .pending n b output (.normal p s) ∧ IsEarlyFor (rules K (decode t θ)) p s (leaf,j) := by
  apply ControllerEarlyRealization.original_early_realized P (rules K (decode t θ))
    (ordinaryJet (scalar K t (decode t θ))) (richJet (scalar K t (decode t θ)))
    (completedOrdinary K t θ) (completedRich K t θ)
    (fun s => Ready s ∧ LastChildClosed (TaskState.retired s)) _ _ _ N seed TaskState.initial _ (leaf,j) he
  · intro s hs p
    exact ⟨serve_ready _ p hs.1 hell,(serve_lastChildClosed K (decode t θ) p s hs.2).2⟩
  · intro s hs p
    apply serve_completedOrdinary hK t θ s p hs.1 hs.2
    intro leaf
    exact (leafData_valid t (decode t θ) hd ((HierarchyAddresses.leafEquiv t).symm leaf)).2.2.1
  · intro s hs p
    exact serve_completedRich hK t θ s p hs.1 hs.2
  · exact ⟨initial_ready hell,initial_lastChildClosed (by omega)⟩

end GradientHessian.GeometricEarlyRealization
