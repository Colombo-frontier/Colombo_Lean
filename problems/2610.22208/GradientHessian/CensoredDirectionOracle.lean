import GradientHessian.CensoredDirectionOrder
import GradientHessian.CensoredJointOracle

/-! Actual center and memory nondisclosure implies raw-factor erasure of
the full oracle view. All selected matrices are preserved unconditionally. -/

noncomputable section
namespace GradientHessian.CensoredDirection
open Classical HigherHierarchy HierarchyAddresses RawHierarchy CensoredHierarchy
  CensoredOracle ControllerCensor FrontierState TaskState GeometricDisclosure

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)

theorem selectedMatrix_of_numerical (t : ℕ) (p : Plan (4096*J^2) t) (x y : Raw d n r J E H t)
    (he : ∀ q,RawLeafFactor.leafNumerical t x q=RawLeafFactor.leafNumerical t y q) :
    selectedMatrix t p (assemble P B fallback t x)=selectedMatrix t p (assemble P B fallback t y) := by
  unfold CensoredOracle.selectedMatrix
  rw [RawLeafFactor.leaf_A_assemble,RawLeafFactor.leaf_A_assemble,he]

theorem center_controller_sameKnown (h depth : ℕ) (w : Word depth) (i : Fin 8)
    (x y : Raw d n r J E H (h+1+depth))
    (he : (RawCenterFactor.factor h depth w i x).2=(RawCenterFactor.factor h depth w i y).2)
    (before after : State (h+1+depth+1) (4096*J^2+1) ell) (cur : Leaf (h+1+depth+1))
    (hc : TaskState.current before=some cur) (hmono : TaskState.retired before⊆TaskState.retired after)
    (hd : ¬NodeDisclosed after (child (addressedNode (h+1) depth w) (by dsimp [addressedNode]; omega) i)) :
    SameKnown (h+1+depth) (planAt before after cur hc (h+1+depth))
      (coefficients P B fallback (h+1+depth) x) (coefficients P B fallback (h+1+depth) y) :=
  center_sameKnown P B fallback h depth w i _ x y he (hiddenBlock_controller before after cur hc hmono w i hd)

theorem old_controller_sameKnown (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.oldFactor depth w i j x).2=(RawMemoryHierarchyFactor.oldFactor depth w i j y).2)
    (before after : State (0+depth+1) (4096*J^2+1) ell) (cur : Leaf (0+depth+1))
    (hc : TaskState.current before=some cur) (hmono : TaskState.retired before⊆TaskState.retired after)
    (hd : ¬NodeDisclosed after (child (addressedNode 0 depth w) (by dsimp [addressedNode]; omega) i)) :
    SameKnown (0+depth) (planAt before after cur hc (0+depth))
      (coefficients P B fallback (0+depth) x) (coefficients P B fallback (0+depth) y) :=
  old_sameKnown P B fallback depth w i j _ x y he (hiddenBlock_controller before after cur hc hmono w i hd)

theorem inner_controller_sameKnown (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.innerFactor depth w i j k x).2=
      (RawMemoryHierarchyFactor.innerFactor depth w i j k y).2)
    (before after : State (0+depth+1) (4096*J^2+1) ell) (cur target : Leaf (0+depth+1))
    (hc : TaskState.current before=some cur) (hmono : TaskState.retired before⊆TaskState.retired after)
    (hw : ∀ a : Fin depth,target ⟨a.val,by have := a.isLt; omega⟩=w a)
    (hi : target ⟨depth,by omega⟩=i) (hd : ¬TaskDisclosed after target j) :
    SameKnown (0+depth) (planAt before after cur hc (0+depth))
      (coefficients P B fallback (0+depth) x) (coefficients P B fallback (0+depth) y) :=
  inner_sameKnown P B fallback depth w i j k _ x y he
    (hiddenInner_controller before after cur target hc hmono w i j hw hi hd)

theorem center_selectedMatrix_eq (h depth : ℕ) (w : Word depth) (i : Fin 8)
    (p : Plan (4096*J^2) (h+1+depth)) (x y : Raw d n r J E H (h+1+depth))
    (he : (RawCenterFactor.factor h depth w i x).2=(RawCenterFactor.factor h depth w i y).2) :
    selectedMatrix (h+1+depth) p (assemble P B fallback (h+1+depth) x)=
      selectedMatrix (h+1+depth) p (assemble P B fallback (h+1+depth) y) :=
  congrArg LeafCoefficients.A (RawCenterLocality.rest_eq_all_leafData P B fallback h depth w i x y he _)

theorem old_selectedMatrix_eq (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) (p : Plan (4096*J^2) (0+depth))
    (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.oldFactor depth w i j x).2=(RawMemoryHierarchyFactor.oldFactor depth w i j y).2) :
    selectedMatrix (0+depth) p (assemble P B fallback (0+depth) x)=
      selectedMatrix (0+depth) p (assemble P B fallback (0+depth) y) :=
  selectedMatrix_of_numerical P B fallback _ p x y (RawMemoryGlobalLocality.old_all_numerical depth w i j x y he)

theorem inner_selectedMatrix_eq (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) (p : Plan (4096*J^2) (0+depth))
    (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.innerFactor depth w i j k x).2=
      (RawMemoryHierarchyFactor.innerFactor depth w i j k y).2) :
    selectedMatrix (0+depth) p (assemble P B fallback (0+depth) x)=
      selectedMatrix (0+depth) p (assemble P B fallback (0+depth) y) :=
  selectedMatrix_of_numerical P B fallback _ p x y (RawMemoryGlobalLocality.inner_all_numerical depth w i j k x y he)

end GradientHessian.CensoredDirection
