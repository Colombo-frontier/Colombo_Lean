import GradientHessian.CensoredCompletedReplies
import GradientHessian.ControllerPolicyExecution

/-! Original true-jet policy execution realized by the actual geometric
controller. The all-retired completion of the callbacks is used globally;
it agrees with the erased callbacks before each disclosure stopping boundary. -/

noncomputable section
namespace GradientHessian.CensoredOriginalExecution
universe u
open Classical HigherHierarchy HierarchyParameters CensoredOracle ControllerCensor
  FrontierState TaskState TaskSlots ComparisonController GeometricDisclosure GeometricRepair JetLocality
  CensoredPolicy ControllerPolicyDriver ComparisonControllerReplay
open scoped InnerProductSpace

variable {Y E : Type u} {H : ℕ → Type u} {m ell : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
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

theorem completed_guarded_run (K : ℝ) (θ : Parameters Y E H m t)
    (R : Rules (t+1) (m+1) ell (Space Y E H m t) (Action t m))
    (stop : State (t+1) (m+1) ell → Bool)
    (hactive : ∀ s,stop s=false → TaskState.current s≠none)
    (fuel : ℕ) (q : Config (t+1) (m+1) ell S (Space Y E H m t) (Action t m)) :
    run P R stop (completedOrdinary K t θ) (completedRich K t θ) fuel q=
      run P R stop (ordinaryReply K t θ) (richReply K t θ) fuel q := by
  apply ControllerPolicyDriver.run_congr P R R stop rfl rfl
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
  · intro before after hb _ Z
    exact completedOrdinary_active K t θ before after (hactive before hb) Z
  · intro before after hb _ Z
    exact completedRich_active K t θ before after (hactive before hb) Z

omit [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)] in
theorem mark_stop_active (leaf : Leaf (t+1)) (j : Fin (m+1))
    (s : State (t+1) (m+1) ell) (hs : markSupplied leaf j s=false) :
    TaskState.current s≠none := by
  intro hc
  have he := (FrontierState.current_none_iff (TaskState.retired s)).mp hc
  have hn := of_decide_eq_false hs
  exact hn (Or.inl (he ▸ Finset.mem_univ leaf))

variable [CompleteSpace Y]

theorem true_jet_policy_execution {K : ℝ} (hK : 0<K) (θ : Parameters Y E H m t)
    (hd : Valid Y E H m t (decode t θ)) (hell : 0<ell) (N : ℕ) (seed : Seed) :
    run P (rules K (decode t θ)) (fun _ => false) (completedOrdinary K t θ) (completedRich K t θ)
      ((N+1)*(8^(t+1)+4)) (ControllerPolicyDriver.initial P N seed TaskState.initial)=
      .finished
        (P.run (ordinaryJet (scalar K t (decode t θ))) (richJet (scalar K t (decode t θ))) N seed)
        (VisibilityWindow.run (rules (ell := ell) K (decode t θ))
          (ControllerPolicyTrace.withOutput P (ordinaryJet (scalar K t (decode t θ)))
            (richJet (scalar K t (decode t θ))) N seed) TaskState.initial) := by
  apply ControllerPolicyExecution.original_policy_execution P (rules K (decode t θ))
    (ordinaryJet (scalar K t (decode t θ))) (richJet (scalar K t (decode t θ)))
    (completedOrdinary K t θ) (completedRich K t θ)
    (fun s => Ready s ∧ LastChildClosed (TaskState.retired s))
  · intro s hs p
    exact ⟨serve_ready _ p hs.1 hell,(serve_lastChildClosed K (decode t θ) p s hs.2).2⟩
  · intro s hs p
    apply serve_completedOrdinary hK t θ s p hs.1 hs.2
    intro leaf
    exact (leafData_valid t (decode t θ) hd ((HierarchyAddresses.leafEquiv t).symm leaf)).2.2.1
  · intro s hs p
    exact serve_completedRich hK t θ s p hs.1 hs.2
  · exact ⟨initial_ready hell,initial_lastChildClosed (by omega)⟩

end GradientHessian.CensoredOriginalExecution
