import GradientHessian.GeometricRepairActions
import GradientHessian.HierarchyAddresses
import GradientHessian.BoundedNumericalTest

/-! Literal geometric repair tests and the current numerical hit predicate.
The rule constructor takes the actual fixed coefficient tree and no assumed
test oracle. Physical projections are shared by all addresses at one height. -/

noncomputable section
namespace GradientHessian.GeometricRepair
universe u
open Classical FrontierState TaskState GeometricDisclosure HigherHierarchy
open scoped InnerProductSpace

variable {Y E : Type u} {H : ℕ → Type u} {t m ell : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h, NormedAddCommGroup (H h)] [∀ h, InnerProductSpace ℝ (H h)]

def localProjection (h : Fin t) (i : Fin 8) : Space Y E H m t →L[ℝ] H h.val :=
  (parentAt (Space Y E H m h.val) (H h.val) i).comp
    (HierarchyAddresses.dropHeight t (h.val+1) (Nat.succ_le_of_lt h.isLt))

def localCenter (K : ℝ) (data : Data Y E H m t) (h : Fin t)
    (path : Fin (t-(h.val+1)) → Fin 8) (i : Fin 8) : H h.val :=
  radius m K h.val •
    (HierarchyAddresses.dataAtHeight t (h.val+1) (Nat.succ_le_of_lt h.isLt) path data).directions i

def oldDirection (data : Data Y E H m t) (path : Fin t → Fin 8) (i : Fin 8)
    (j : Fin (FirstHeight.depth (m+1)+2)) : E :=
  (HierarchyAddresses.oldData t path data).outerDirections i j

def leafCoefficients (data : Data Y E H m t) (leaf : Leaf (t+1)) : LeafCoefficients Y E m :=
  leafData t data ((HierarchyAddresses.leafEquiv t).symm leaf)

def innerReadout (data : Data Y E H m t) (leaf : Leaf (t+1)) (task : Fin (m+1))
    (j : Fin (Inner.absoluteDepth+2)) (Z : Space Y E H m t) : ℝ :=
  LatchChain.u (Inner.radius Inner.absoluteDepth j) ((leafCoefficients data leaf).v task j)
    (HierarchyAddresses.innerRegisterProjection t task j Z)

def oldReadout (data : Data Y E H m t) (path : Fin t → Fin 8) (i : Fin 8)
    (j : Fin (FirstHeight.depth (m+1)+2)) (Z : Space Y E H m t) : ℝ :=
  LatchChain.u (Inner.radius (FirstHeight.depth (m+1)) j) (oldDirection data path i j)
    (HierarchyAddresses.oldRegisterProjection t i j Z)

def markReadout (data : Data Y E H m t) (leaf : Leaf (t+1)) (task : Fin (m+1))
    (Z : Space Y E H m t) : ℝ :=
  ⟪(leafCoefficients data leaf).a task,
    BoundedNumericalTest.test (HierarchyAddresses.numericalProjection t Z)⟫_ℝ

def trigger (K : ℝ) (data : Data Y E H m t) (s : State (t+1) (m+1) ell)
    (Z : Space Y E H m t) : Action t m → Bool
  | .localized h path i => decide
      (Visible (TaskState.retired s) (localNode h path) ∧
       ¬NodeDisclosed s (localChild h path i) ∧
       ‖localProjection h i Z-localCenter K data h path i‖ ≤ 3*width m h.val)
  | .old path i j => decide
      (Visible (TaskState.retired s) (oldNode path) ∧
       ¬NodeDisclosed s (oldChild path i) ∧ 1/8 < |oldReadout data path i j Z|)
  | .inner leaf task j => decide
      (TaskState.current s=some leaf ∧ ¬TaskDisclosed s leaf task ∧ 1/8< |innerReadout data leaf task j Z|)
  | .futureMark leaf task => decide
      (TaskState.current s=some leaf ∧ ¬MarkSupplied s leaf task ∧ 1/3072< |markReadout data leaf task Z|)

def hit (data : Data Y E H m t) (s : State (t+1) (m+1) ell) (Z : Space Y E H m t) : Bool :=
  match hc : TaskState.current s with
  | none => false
  | some leaf => decide (1/3072< |markReadout data leaf
      ⟨(s.completed leaf).val,TaskState.current_live s hc⟩ Z|)

def rules (K : ℝ) (data : Data Y E H m t) :
    ComparisonController.Rules (t+1) (m+1) ell (Space Y E H m t) (Action t m) where
  priority := priority t m
  target := target
  trigger := trigger K data
  hit := hit data

theorem hit_current (data : Data Y E H m t) (s : State (t+1) (m+1) ell)
    (Z : Space Y E H m t) {leaf : Leaf (t+1)} (hc : TaskState.current s=some leaf) :
    hit data s Z = decide (1/3072< |markReadout data leaf
      ⟨(s.completed leaf).val,TaskState.current_live s hc⟩ Z|) := by
  unfold hit
  split
  · rename_i hn
    simp [hc] at hn
  · rename_i leaf' he
    have hl : leaf'=leaf := by simpa only [hc,Option.some.injEq] using he.symm
    subst leaf'
    rfl

theorem trigger_has_unretired_target (K : ℝ) (data : Data Y E H m t)
    (s : State (t+1) (m+1) ell) (Z : Space Y E H m t) (a : Action t m)
    (ha : trigger K data s Z a=true) : (subtree (target a) \ TaskState.retired s).Nonempty := by
  apply Finset.sdiff_nonempty.mpr
  intro hr
  cases a with
  | localized h path i =>
    have hh : Visible (TaskState.retired s) (localNode h path) ∧
        ¬NodeDisclosed s (localChild h path i) ∧
        ‖localProjection h i Z-localCenter K data h path i‖≤3*width m h.val := by
      simpa only [trigger,decide_eq_true_eq] using ha
    exact hh.2.1 ((localChild_subset_target (m := m) h path i).trans hr)
  | old path i j =>
    have hh : Visible (TaskState.retired s) (oldNode path) ∧
        ¬NodeDisclosed s (oldChild path i) ∧ 1/8< |oldReadout data path i j Z| := by
      simpa only [trigger,decide_eq_true_eq] using ha
    exact hh.2.1 ((subtree_child_subset _ _ i).trans hr)
  | inner leaf task j =>
    have hc : TaskState.current s=some leaf := by
      simpa only [trigger,decide_eq_true_eq] using (show
        TaskState.current s=some leaf ∧ ¬TaskDisclosed s leaf task ∧
          1/8< |innerReadout data leaf task j Z| from by simpa only [trigger,decide_eq_true_eq] using ha).1
    exact ((current_eq_some_iff _ _).mp hc).1 (hr (by simp [target]))
  | futureMark leaf task =>
    have hh : TaskState.current s=some leaf ∧ ¬MarkSupplied s leaf task ∧
        1/3072< |markReadout data leaf task Z| := by simpa only [trigger,decide_eq_true_eq] using ha
    exact ((current_eq_some_iff _ _).mp hh.1).1 (hr (by simp [target]))

theorem terminal_trigger_false (K : ℝ) (data : Data Y E H m t)
    (s : State (t+1) (m+1) ell) (p : ComparisonController.Pending (Space Y E H m t))
    (ht : ComparisonController.choose (rules K data) p s=none) (a : Action t m) :
    trigger K data s p.point a=false := by
  cases ha : trigger K data s p.point a with
  | false => rfl
  | true =>
    have hr := (ComparisonController.choose_none_iff (rules K data) p s).mp ht a (mem_priority a) ha
    obtain ⟨leaf,hl⟩ := trigger_has_unretired_target K data s p.point a ha
    exact False.elim ((Finset.mem_sdiff.mp hl).2 (hr (Finset.mem_sdiff.mp hl).1))

end GradientHessian.GeometricRepair

