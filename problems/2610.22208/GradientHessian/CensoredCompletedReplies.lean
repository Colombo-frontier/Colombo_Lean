import GradientHessian.CensoredPolicyReplies
import GradientHessian.ControllerPolicyDriver

/-! Complete the callbacks by the true jet on empty frontiers. This makes
actual receipts correct globally. Every stopped run whose open states have
a live frontier agrees with the original erased callbacks. -/

noncomputable section
namespace GradientHessian.CensoredPolicy
universe u
open Classical HigherHierarchy HierarchyParameters CensoredOracle ControllerCensor
  FrontierState TaskState TaskSlots ComparisonController GeometricDisclosure GeometricRepair JetLocality
open scoped InnerProductSpace

variable {Y E : Type u} {H : ℕ → Type u} {m ell : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]

def completedOrdinary (K : ℝ) (t : ℕ) (θ : Parameters Y E H m t)
    (before after : State (t+1) (m+1) ell) (Z : Space Y E H m t) :
    ℝ × (Space Y E H m t →L[ℝ] ℝ) :=
  if TaskState.current before=none then ordinaryJet (HigherHierarchy.scalar K t (decode t θ)) Z
  else ordinaryReply K t θ before after Z

def completedRich (K : ℝ) (t : ℕ) (θ : Parameters Y E H m t)
    (before after : State (t+1) (m+1) ell) (Z : Space Y E H m t) :
    ℝ × (Space Y E H m t →L[ℝ] ℝ) × (Space Y E H m t →L[ℝ] Space Y E H m t →L[ℝ] ℝ) :=
  if TaskState.current before=none then richJet (HigherHierarchy.scalar K t (decode t θ)) Z
  else richReply K t θ before after Z

theorem completedOrdinary_active (K : ℝ) (t : ℕ) (θ : Parameters Y E H m t)
    (before after : State (t+1) (m+1) ell) (hc : TaskState.current before≠none) (Z : Space Y E H m t) :
    completedOrdinary K t θ before after Z=ordinaryReply K t θ before after Z := by
  simp only [completedOrdinary,if_neg hc]

theorem completedRich_active (K : ℝ) (t : ℕ) (θ : Parameters Y E H m t)
    (before after : State (t+1) (m+1) ell) (hc : TaskState.current before≠none) (Z : Space Y E H m t) :
    completedRich K t θ before after Z=richReply K t θ before after Z := by
  simp only [completedRich,if_neg hc]

theorem serve_completedRich {K : ℝ} (hK : 0<K) (t : ℕ) (θ : Parameters Y E H m t)
    (s : State (t+1) (m+1) ell) (q : Pending (Space Y E H m t)) (hs : Ready s)
    (hclosed : LastChildClosed (TaskState.retired s)) :
    completedRich K t θ (serve (rules K (decode t θ)) q s).beforeNormal
      (serve (rules K (decode t θ)) q s).afterNormal q.point=
      richJet (HigherHierarchy.scalar K t (decode t θ)) q.point := by
  cases hc : TaskState.current (serve (rules K (decode t θ)) q s).beforeNormal with
  | none => simp only [completedRich,hc,if_true]
  | some leaf =>
    rw [completedRich_active K t θ _ _ (by simp [hc])]
    exact (serve_richReply hK t θ s q hs hclosed leaf hc).symm

variable [CompleteSpace Y]

theorem serve_completedOrdinary {K : ℝ} (hK : 0<K) (t : ℕ) (θ : Parameters Y E H m t)
    (s : State (t+1) (m+1) ell) (q : Pending (Space Y E H m t)) (hs : Ready s)
    (hclosed : LastChildClosed (TaskState.retired s))
    (hsym : ∀ leaf x z,⟪(leafCoefficients (decode t θ) leaf).A x,z⟫_ℝ=
      ⟪x,(leafCoefficients (decode t θ) leaf).A z⟫_ℝ) :
    completedOrdinary K t θ (serve (rules K (decode t θ)) q s).beforeNormal
      (serve (rules K (decode t θ)) q s).afterNormal q.point=
      ordinaryJet (HigherHierarchy.scalar K t (decode t θ)) q.point := by
  cases hc : TaskState.current (serve (rules K (decode t θ)) q s).beforeNormal with
  | none => simp only [completedOrdinary,hc,if_true]
  | some leaf =>
    rw [completedOrdinary_active K t θ _ _ (by simp [hc])]
    exact (serve_ordinaryReply hK t θ s q hs hclosed leaf hc (hsym leaf)).symm

end GradientHessian.CensoredPolicy
