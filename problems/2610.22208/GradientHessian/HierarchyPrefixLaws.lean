import GradientHessian.ControllerCensorPlan
import GradientHessian.HierarchyAddressLaws

/-! Composition laws for coefficient prefixes and shared physical lower
projections. Appending a word digit selects one child of the preceding node. -/

noncomputable section
namespace GradientHessian.HierarchyAddresses
universe u
open Classical HigherHierarchy

variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h, NormedAddCommGroup (H h)] [∀ h, InnerProductSpace ℝ (H h)]

theorem castSpace_lower {a b : ℕ} (hab : a=b) (Z : Space Y E H m (a+1)) :
    lower (Space Y E H m b) (H b) (castSpace (congrArg Nat.succ hab) Z)=
      castSpace hab (lower (Space Y E H m a) (H a) Z) := by
  subst b
  rfl

@[simp] theorem castData_refl (a : ℕ) (x : Data Y E H m a) : castData rfl x=x := rfl

@[simp] theorem castData_trans {a b c : ℕ} (hab : a=b) (hbc : b=c) (x : Data Y E H m a) :
    castData hbc (castData hab x)=castData (hab.trans hbc) x := by subst b; subst c; rfl

@[simp] theorem castSpace_refl (a : ℕ) (x : Space Y E H m a) : castSpace rfl x=x := rfl

@[simp] theorem castSpace_trans {a b c : ℕ} (hab : a=b) (hbc : b=c) (x : Space Y E H m a) :
    castSpace hbc (castSpace hab x)=castSpace (hab.trans hbc) x := by subst b; subst c; rfl

theorem dataAt_cast_depth (h : ℕ) {a b : ℕ} (hab : a=b) (w : Word a) (d : Data Y E H m (h+a)) :
    dataAt h a w d=dataAt h b (fun i => w (i.cast hab.symm))
      (castData (congrArg (h+·) hab) d) := by subst b; rfl

theorem dropPrefix_cast_depth (h : ℕ) {a b : ℕ} (hab : a=b) (Z : Space Y E H m (h+a)) :
    dropPrefix h a Z=dropPrefix h b (castSpace (congrArg (h+·) hab) Z) := by subst b; rfl

theorem dataAt_last (h : ℕ) : ∀ (depth : ℕ) (w : Word (depth+1))
    (x : Data Y E H m (h+depth+1)),
    dataAt h (depth+1) w x =
      (dataAt (h+1) depth (Fin.init w) (castData (by omega) x)).children (w (Fin.last depth))
  | 0,w,x => rfl
  | depth+1,w,x => by
    change dataAt h (depth+1) (Fin.tail w) (x.children (w 0)) =
      (dataAt (h+1) depth (Fin.tail (Fin.init w))
        ((castData (congrArg Nat.succ (show h+depth+1=h+1+depth by omega)) x).children (w 0))).children
          (w (Fin.last (depth+1)))
    rw [castData_children]
    exact dataAt_last h depth (Fin.tail w) (x.children (w 0))

theorem dropPrefix_last (h : ℕ) : ∀ (depth : ℕ) (Z : Space Y E H m (h+depth+1)),
    dropPrefix h (depth+1) Z = lower (Space Y E H m h) (H h)
      (dropPrefix (h+1) depth (castSpace (by omega) Z))
  | 0,Z => rfl
  | depth+1,Z => by
    change dropPrefix h (depth+1) (lower (Space Y E H m (h+depth+1)) (H (h+depth+1)) Z) =
      lower (Space Y E H m h) (H h) (dropPrefix (h+1) depth
        (lower (Space Y E H m (h+1+depth)) (H (h+1+depth))
          (castSpace (congrArg Nat.succ (show h+depth+1=h+1+depth by omega)) Z)))
    rw [castSpace_lower]
    exact dropPrefix_last h depth (lower (Space Y E H m (h+depth+1)) (H (h+depth+1)) Z)

theorem dataAtHeight_current_child {t h : ℕ} (hh : h+1≤t) (leaf : FrontierState.Leaf (t+1))
    (d : Data Y E H m t) :
    dataAtHeight t h (by omega) (ControllerCensor.pathPrefix leaf h) d =
      (dataAtHeight t (h+1) hh (ControllerCensor.pathPrefix leaf (h+1)) d).children
        (ControllerCensor.currentChild leaf (h+1)) := by
  obtain ⟨depth,rfl⟩ := Nat.exists_eq_add_of_le hh
  have he1 : h+1+depth-h=depth+1 := by omega
  have he2 : h+1+depth-(h+1)=depth := by omega
  unfold dataAtHeight
  rw [dataAt_cast_depth h he1,dataAt_cast_depth (h+1) he2]
  rw [dataAt_last]
  simp only [castData_trans,castData_refl]
  congr 2
  dsimp only [ControllerCensor.pathPrefix,ControllerCensor.currentChild]
  apply congrArg leaf
  apply Fin.ext
  exact he2.symm

theorem dropHeight_lower {t h : ℕ} (hh : h+1≤t) (Z : Space Y E H m t) :
    dropHeight t h (by omega) Z = lower (Space Y E H m h) (H h) (dropHeight t (h+1) hh Z) := by
  obtain ⟨depth,rfl⟩ := Nat.exists_eq_add_of_le hh
  have he1 : h+1+depth-h=depth+1 := by omega
  have he2 : h+1+depth-(h+1)=depth := by omega
  simp only [dropHeight,ContinuousLinearMap.comp_apply]
  rw [dropPrefix_cast_depth h he1,dropPrefix_cast_depth (h+1) he2]
  rw [dropPrefix_last]
  simp only [castSpace_trans,castSpace_refl]
  apply congrArg (fun V => lower (Space Y E H m h) (H h) (dropPrefix (h+1) depth V))
  exact (castSpace_trans (Y := Y) (E := E) (H := H) (m := m) _ _ Z).trans (by rfl)

theorem dataAtHeight_self (t : ℕ) (leaf : FrontierState.Leaf (t+1)) (d : Data Y E H m t) :
    dataAtHeight t t le_rfl (ControllerCensor.pathPrefix leaf t) d=d := by
  unfold dataAtHeight
  rw [dataAt_cast_depth t (Nat.sub_self t)]
  simp only [dataAt,castData_trans,castData_refl]

theorem dropHeight_self (t : ℕ) (Z : Space Y E H m t) : dropHeight t t le_rfl Z=Z := by
  simp only [dropHeight,ContinuousLinearMap.comp_apply]
  rw [dropPrefix_cast_depth t (Nat.sub_self t)]
  simp only [dropPrefix,castSpace_trans,castSpace_refl,ContinuousLinearMap.id_apply]
  rfl

theorem leafData_old_last : ∀ (t : ℕ) (w : Word (t+1)) (d : Data Y E H m t),
    leafData t d (wordLeaf t w)=leafData (H := H) 0 (oldData t (Fin.init w) d) (w (Fin.last t))
  | 0,w,d => rfl
  | t+1,w,d => by
    change leafData t (d.children (w 0)) (wordLeaf t (Fin.tail w)) = _
    rw [oldData_succ]
    exact leafData_old_last t (Fin.tail w) (d.children (w 0))

theorem leafCoefficients_old (t : ℕ) (leaf : FrontierState.Leaf (t+1)) (d : Data Y E H m t) :
    GeometricRepair.leafCoefficients d leaf=
      leafData (H := H) 0 (oldData t (ControllerCensor.pathPrefix leaf 0) d)
        (ControllerCensor.currentChild leaf 0) :=
  leafData_old_last t (ofLex leaf) d

theorem oldProjection_succ_apply (t : ℕ) (Z : Space Y E H m (t+1)) :
    oldProjection (t+1) Z=oldProjection t (lower (Space Y E H m t) (H t) Z) := by
  change dropPrefix 0 t
      (lower (Space Y E H m (0+t)) (H (0+t))
        (castSpace (congrArg Nat.succ (Nat.zero_add t).symm) Z)) =
    dropPrefix 0 t (castSpace (Nat.zero_add t).symm (lower (Space Y E H m t) (H t) Z))
  rw [castSpace_lower]

theorem numericalProjection_succ (t : ℕ) :
    numericalProjection (Y := Y) (E := E) (H := H) (m := m) (t+1)=
      (numericalProjection t).comp (lower (Space Y E H m t) (H t)) := by
  ext Z
  simp only [numericalProjection,leafProjection,ContinuousLinearMap.comp_apply,oldProjection_succ_apply]
  rfl

end GradientHessian.HierarchyAddresses
