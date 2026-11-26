import GradientHessian.DirectionSlotIdentification
import GradientHessian.DirectionPolicyReplay
import GradientHessian.GeometricDisclosureStops

/-! Canonical source actions for the three isolated direction factors.
Their slots and disclosure stops agree with the literal comparison rules. -/

noncomputable section
namespace GradientHessian.GeometricRepair
open Classical HigherHierarchy HierarchyAddresses RawDirection FrontierState

def centerFactorAction {J : ℕ} (h depth : ℕ) (w : Word depth) (i : Fin 8) :
    Action (h+1+depth) (4096*J^2) :=
  .localized ⟨h,by omega⟩ (fun a => w ⟨a.val,by
    have ha := a.isLt
    change a.val<h+1+depth-(h+1) at ha
    omega⟩) i

def oldFactorAction {J : ℕ} (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) : Action (0+depth) (4096*J^2) :=
  .old (fun a => w ⟨a.val,by have := a.isLt; omega⟩) i j

def innerFactorAction {J : ℕ} (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) : Action (0+depth) (4096*J^2) :=
  .inner (leafEquiv (0+depth) (prependSlot 0 depth w i)) j k

theorem cast_embed_depth {J h a b : ℕ} (he : a=b) (w : Word b) (q : Slot J h) :
    castSlot (congrArg (fun k => h+k) he) (embed h a (fun k => w (Fin.cast he k)) q)=embed h b w q := by
  subst b
  rfl

theorem address_depth_cast {L a b : ℕ} (he : a=b) (ha : a<L+1) (hb : b<L+1) (w : Word b) :
    (⟨⟨a,ha⟩,fun k => w (Fin.cast he k)⟩ : Node L)=⟨⟨b,hb⟩,w⟩ := by
  subst b
  rfl

theorem child_node_congr {L : ℕ} {v w : Node L} (he : v=w) (i : Fin 8)
    {hv : v.1.val<L} {hw : w.1.val<L} : child v hv i=child w hw i := by
  subst w
  rfl

theorem centerFactorAction_slot {J : ℕ} (h depth : ℕ) (w : Word depth) (i : Fin 8) :
    directionSlot (centerFactorAction (J := J) h depth w i)=some (embed (h+1) depth w (.inr i)) := by
  apply congrArg some
  exact cast_embed_depth (h := h+1) (a := h+1+depth-(h+1)) (b := depth) (by omega) w (.inr i)

theorem oldFactorAction_slot {J : ℕ} (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) :
    directionSlot (oldFactorAction depth w i j)=some (embed 0 depth w (.inl (i,j))) := by
  apply congrArg some
  exact cast_embed_depth (h := 0) (a := 0+depth) (b := depth) (by omega) w (.inl (i,j))

theorem innerSlot_prepend {J : ℕ} : ∀ (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)),
    innerSlot (0+depth) (prependSlot 0 depth w i) j k=embed 0 depth w (.inr (i,j,k))
  | 0,_,_,_,_ => rfl
  | depth+1,w,i,j,k => congrArg (fun q => Sum.inl (w 0,q)) (innerSlot_prepend depth (Fin.tail w) i j k)

theorem innerFactorAction_slot {J : ℕ} (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) :
    directionSlot (innerFactorAction depth w i j k)=some (embed 0 depth w (.inr (i,j,k))) := by
  simp only [innerFactorAction,directionSlot,Equiv.symm_apply_apply,innerSlot_prepend]

theorem centerFactor_block_single {J : ℕ} (h depth : ℕ) (w : Word depth) (i : Fin 8) :
    blockDirection (embed (h+1) depth w (.inr i))=
      (fun a => decide (a=centerFactorAction (J := J) h depth w i)) :=
  blockDirection_eq_single _ _ (centerFactorAction_slot h depth w i)

theorem oldFactor_block_single {J : ℕ} (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) :
    blockDirection (embed 0 depth w (.inl (i,j)))=(fun a => decide (a=oldFactorAction depth w i j)) :=
  blockDirection_eq_single _ _ (oldFactorAction_slot depth w i j)

theorem innerFactor_block_single {J : ℕ} (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) :
    blockDirection (embed 0 depth w (.inr (i,j,k)))=(fun a => decide (a=innerFactorAction depth w i j k)) :=
  blockDirection_eq_single _ _ (innerFactorAction_slot depth w i j k)

theorem centerFactorAction_stop {J ell : ℕ} (h depth : ℕ) (w : Word depth) (i : Fin 8) :
    actionStop (ell := ell) (centerFactorAction (J := J) h depth w i)=DirectionPolicyReplay.centerStop h depth w i := by
  have hn : localNode (⟨h,by omega⟩ : Fin (h+1+depth))
      (fun a => w ⟨a.val,by have ha := a.isLt; change a.val<h+1+depth-(h+1) at ha; omega⟩)=
      CensoredDirection.addressedNode (h+1) depth w :=
    address_depth_cast (a := h+1+depth-(h+1)) (b := depth) (by omega) _ _ w
  simp only [centerFactorAction,actionStop,localChild,DirectionPolicyReplay.centerStop]
  exact congrArg DirectionPolicy.nodeStop (child_node_congr hn i)

theorem oldFactorAction_stop {J ell : ℕ} (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) :
    actionStop (ell := ell) (oldFactorAction depth w i j)=DirectionPolicyReplay.oldStop depth w i := by
  have hn : oldNode (fun a : Fin (0+depth) => w ⟨a.val,by have := a.isLt; omega⟩)=
      CensoredDirection.addressedNode 0 depth w := address_depth_cast (by omega) _ _ w
  simp only [oldFactorAction,actionStop,oldChild,DirectionPolicyReplay.oldStop]
  exact congrArg DirectionPolicy.nodeStop (child_node_congr hn i)

theorem innerFactorAction_stop {J ell : ℕ} (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) :
    actionStop (ell := ell) (innerFactorAction depth w i j k)=
      ComparisonControllerReplay.taskDisclosed (leafEquiv (0+depth) (prependSlot 0 depth w i)) j := rfl

end GradientHessian.GeometricRepair
