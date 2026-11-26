import GradientHessian.DirectionPolicyReplies
import GradientHessian.CensoredDirectionOracle
import GradientHessian.GeometricDirectionErasure

/-! Actual presampled center and memory replacement preserves both total
reply callbacks before disclosure. Arbitrary impossible snapshot pairs are
handled by the public retirement guard. -/

noncomputable section
namespace GradientHessian.DirectionPolicy
open Classical HigherHierarchy HierarchyAddresses RawHierarchy CensoredHierarchy
  ControllerCensor FrontierState TaskState GeometricDisclosure CensoredDirection

def nodeStop {L M ell : ℕ} (v : Node L) (s : State L M ell) : Bool := decide (NodeDisclosed s v)

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)

theorem center_replies_eq {K : ℝ} (hK : 0<K) (h depth : ℕ) (w : Word depth) (i : Fin 8)
    (x y : Raw d n r J E H (h+1+depth))
    (he : (RawCenterFactor.factor h depth w i x).2=(RawCenterFactor.factor h depth w i y).2)
    (before after : State (h+1+depth+1) (4096*J^2+1) ell)
    (hs : nodeStop (child (addressedNode (h+1) depth w) (by dsimp [addressedNode]; omega) i) after=false)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) (h+1+depth)) :
    ordinary K (h+1+depth) (coefficients P B fallback (h+1+depth) x) before after Z=
      ordinary K (h+1+depth) (coefficients P B fallback (h+1+depth) y) before after Z ∧
    rich K (h+1+depth) (coefficients P B fallback (h+1+depth) x) before after Z=
      rich K (h+1+depth) (coefficients P B fallback (h+1+depth) y) before after Z := by
  have hd := of_decide_eq_false hs
  apply replies_eq hK
  · intro hm
    exact active_of_hidden_node before after hm _ hd
  · intro hm cur hc
    exact center_controller_sameKnown P B fallback h depth w i x y he before after cur hc hm hd
  · intro p
    simpa only [decode_coefficients] using center_selectedMatrix_eq P B fallback h depth w i p x y he

theorem old_replies_eq {K : ℝ} (hK : 0<K) (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.oldFactor depth w i j x).2=(RawMemoryHierarchyFactor.oldFactor depth w i j y).2)
    (before after : State (0+depth+1) (4096*J^2+1) ell)
    (hs : nodeStop (child (addressedNode 0 depth w) (by dsimp [addressedNode]; omega) i) after=false)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) (0+depth)) :
    ordinary K (0+depth) (coefficients P B fallback (0+depth) x) before after Z=
      ordinary K (0+depth) (coefficients P B fallback (0+depth) y) before after Z ∧
    rich K (0+depth) (coefficients P B fallback (0+depth) x) before after Z=
      rich K (0+depth) (coefficients P B fallback (0+depth) y) before after Z := by
  have hd := of_decide_eq_false hs
  apply replies_eq hK
  · intro hm
    exact active_of_hidden_node before after hm _ hd
  · intro hm cur hc
    exact old_controller_sameKnown P B fallback depth w i j x y he before after cur hc hm hd
  · intro p
    simpa only [decode_coefficients] using old_selectedMatrix_eq P B fallback depth w i j p x y he

theorem inner_replies_eq {K : ℝ} (hK : 0<K) (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.innerFactor depth w i j k x).2=
      (RawMemoryHierarchyFactor.innerFactor depth w i j k y).2)
    (before after : State (0+depth+1) (4096*J^2+1) ell) (target : Leaf (0+depth+1))
    (hw : ∀ a : Fin depth,target ⟨a.val,by have := a.isLt; omega⟩=w a)
    (hi : target ⟨depth,by omega⟩=i)
    (hs : ComparisonControllerReplay.taskDisclosed target j after=false)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) (0+depth)) :
    ordinary K (0+depth) (coefficients P B fallback (0+depth) x) before after Z=
      ordinary K (0+depth) (coefficients P B fallback (0+depth) y) before after Z ∧
    rich K (0+depth) (coefficients P B fallback (0+depth) x) before after Z=
      rich K (0+depth) (coefficients P B fallback (0+depth) y) before after Z := by
  have hd : ¬TaskDisclosed after target j := by
    have hh : ¬j.val<(after.completed target).val := of_decide_eq_false hs
    exact hh
  apply replies_eq hK
  · intro hm
    exact active_of_hidden_task before after hm target j hd
  · intro hm cur hc
    exact inner_controller_sameKnown P B fallback depth w i j k x y he before after cur target hc hm hw hi hd
  · intro p
    simpa only [decode_coefficients] using inner_selectedMatrix_eq P B fallback depth w i j k p x y he

end GradientHessian.DirectionPolicy
