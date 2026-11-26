import GradientHessian.GeometricTerminalPlateaus
import GradientHessian.HigherHierarchyActivation

/-! A true small-gradient selected point forces complete retirement after
the literal repair pass. This uses actual root activation and the terminal
outgoing plateau, independently of the adaptive decoder construction. -/

noncomputable section
namespace GradientHessian.GeometricRepair
universe u
open Classical FrontierState TaskState GeometricDisclosure HigherHierarchy ComparisonController
open Filter
open scoped Topology

variable {Y E : Type u} {H : ℕ → Type u} {t m ell : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h, NormedAddCommGroup (H h)] [∀ h, InnerProductSpace ℝ (H h)]

omit [∀ h, InnerProductSpace ℝ (H h)] in
theorem root_data_cast (t n : ℕ) (hn : n=0) (he : t+n=t) (w : Fin n → Fin 8)
    (d : Data Y E H m t) :
    HierarchyAddresses.dataAt t n w (HierarchyAddresses.castData he.symm d)=d := by
  subst n
  rfl

theorem root_space_cast (t n : ℕ) (hn : n=0) (he : t+n=t) (Z : Space Y E H m t) :
    HierarchyAddresses.dropPrefix t n (HierarchyAddresses.castSpace he.symm Z)=Z := by
  subst n
  rfl

theorem terminal_root_outgoing_zero (K : ℝ) (data : Data Y E H m t)
    (s : State (t+1) (m+1) ell) (p : Pending (Space Y E H m t))
    (ht : choose (rules K data) p s=none) (hs : LastChildClosed (TaskState.retired s))
    (leaf : Leaf (t+1)) (hc : TaskState.current s=some leaf) : outgoing K t data p.point=0 := by
  cases t with
  | zero =>
    let path : Fin 0 → Fin 8 := fun j => Fin.elim0 j
    have hv : Visible (TaskState.retired s) (oldNode path) := ⟨leaf,hc,fun j => Fin.elim0 j⟩
    have hz := (terminal_visible_old_outgoing_zero_near K data s p ht hs path hv).eq_of_nhds
    simpa only [HierarchyAddresses.oldData,HierarchyAddresses.dataAtHeight,
      HierarchyAddresses.dataAt,HierarchyAddresses.castData,HierarchyAddresses.oldProjection,
      HierarchyAddresses.dropHeight,HierarchyAddresses.dropPrefix,HierarchyAddresses.castSpace,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using hz
  | succ t =>
    let h : Fin (t+1) := ⟨t,by omega⟩
    let path : Fin ((t+1)-(h.val+1)) → Fin 8 := fun j => False.elim (by have := j.isLt; dsimp [h] at *; omega)
    have hv : Visible (TaskState.retired s) (localNode h path) := by
      refine ⟨leaf,hc,?_⟩
      intro j
      have hj := j.isLt
      simp only [localNode,h] at hj
      omega
    have hz := (terminal_visible_localized_outgoing_zero_near K data s p ht hs h path hv).eq_of_nhds
    have hdroot : HierarchyAddresses.dataAtHeight (t+1) (t+1) le_rfl path data=data :=
      root_data_cast (t+1) ((t+1)-(t+1)) (Nat.sub_self _) (Nat.add_sub_of_le le_rfl) path data
    have hproot : HierarchyAddresses.dropHeight (Y := Y) (E := E) (H := H) (m := m)
        (t+1) (t+1) le_rfl p.point=p.point :=
      root_space_cast (t+1) ((t+1)-(t+1)) (Nat.sub_self _) (Nat.add_sub_of_le le_rfl) p.point
    change outgoing K (t+1) (HierarchyAddresses.dataAtHeight (t+1) (t+1) le_rfl path data)
      (HierarchyAddresses.dropHeight (t+1) (t+1) le_rfl p.point)=0 at hz
    rw [hdroot,hproot] at hz
    exact hz

variable [CompleteSpace Y] [CompleteSpace E] [∀ h, CompleteSpace (H h)]

theorem terminal_small_gradient_retired {K : ℝ} (hK : 16≤K) (data : Data Y E H m t)
    (hd : Valid Y E H m t data) (s : State (t+1) (m+1) ell) (p : Pending (Space Y E H m t))
    (ht : choose (rules K data) p s=none) (hs : LastChildClosed (TaskState.retired s))
    (hg : ‖gradient (HigherHierarchy.scalar K t data) p.point‖≤1) :
    TaskState.retired s=Finset.univ := by
  cases hc : TaskState.current s with
  | none => exact (FrontierState.current_none_iff _).mp hc
  | some leaf =>
    have hz := terminal_root_outgoing_zero K data s p ht hs leaf hc
    have hd0 : HigherHierarchy.driven K t data 0=HigherHierarchy.scalar K t data := by
      funext Z
      simp only [HigherHierarchy.driven,zero_mul,sub_zero]
    have ho := activation_outgoing_one hK t data hd (l := 0) (by norm_num) p.point
      (by rw [hd0]; exact hg)
    linarith

theorem serve_small_gradient_retired {K : ℝ} (hK : 16≤K) (data : Data Y E H m t)
    (hd : Valid Y E H m t data) (s : State (t+1) (m+1) ell) (p : Pending (Space Y E H m t))
    (hs : LastChildClosed (TaskState.retired s))
    (hg : ‖gradient (HigherHierarchy.scalar K t data) p.point‖≤1) :
    TaskState.retired (serve (rules K data) p s).beforeNormal=Finset.univ :=
  terminal_small_gradient_retired hK data hd _ p (serve_terminal (rules K data) p s)
    (serve_lastChildClosed K data p s hs).1 hg

theorem serve_small_gradient_after_retired {K : ℝ} (hK : 16≤K) (data : Data Y E H m t)
    (hd : Valid Y E H m t data) (s : State (t+1) (m+1) ell) (p : Pending (Space Y E H m t))
    (hs : LastChildClosed (TaskState.retired s))
    (hg : ‖gradient (HigherHierarchy.scalar K t data) p.point‖≤1) :
    TaskState.retired (serve (rules K data) p s).afterNormal=Finset.univ := by
  have hb := serve_small_gradient_retired hK data hd s p hs hg
  have hc : TaskState.current (serve (rules K data) p s).beforeNormal=none :=
    (FrontierState.current_none_iff _).mpr hb
  have ha : (serve (rules K data) p s).afterNormal=(serve (rules K data) p s).beforeNormal := by
    change normal (rules K data) p (serve (rules K data) p s).beforeNormal=_
    cases hk : p.kind <;> simp only [normal,hk,TaskSlots.ordinaryStep,richComplete,hc]
  rw [ha]
  exact hb

end GradientHessian.GeometricRepair
