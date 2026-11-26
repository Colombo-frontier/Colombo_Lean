import GradientHessian.GeometricRepairRules
import GradientHessian.GeometricDisclosureStops

/-! The complete public disclosure packet of the stronger comparison
oracle. The masks include every retired subtree, even beyond the frontier.
All coefficients are actual scalar coefficients; a zero entry is accompanied
by the public controller state determining whether that entry is disclosed. -/

noncomputable section
namespace GradientHessian.AugmentedDisclosure
open Classical HigherHierarchy FrontierState TaskState GeometricRepair GeometricDisclosure

universe u
variable (Y E : Type u) (H : ℕ → Type u) (t m ell : ℕ)
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]

def DirectionValue : Action t m → Type u
  | .localized h _ _ => H h.val
  | .old _ _ _ | .inner _ _ _ | .futureMark _ _ => E

instance directionZero (a : Action t m) : Zero (DirectionValue E H t m a) := by
  cases a <;> dsimp [DirectionValue] <;> infer_instance

abbrev View := State (t+1) (m+1) ell ×
  (Leaf (t+1) → Y →L[ℝ] Y) ×
  (Leaf (t+1) → Fin (m+1) → Y) ×
  (Leaf (t+1) → Fin (m+1) → Y) ×
  ((a : Action t m) → DirectionValue E H t m a)

variable {Y E H t m ell}

def directionDisclosed (s : State (t+1) (m+1) ell) : Action t m → Prop
  | .localized h w i => NodeDisclosed s (localChild h w i)
  | .old w i _ => NodeDisclosed s (oldChild w i)
  | .inner leaf j _ => TaskDisclosed s leaf j
  | .futureMark _ _ => False

def direction (K : ℝ) (data : Data Y E H m t) : (a : Action t m) → DirectionValue E H t m a
  | .localized h w i => localCenter (Y := Y) (E := E) (H := H) K data h w i
  | .old w i j => oldDirection (Y := Y) (E := E) (H := H) data w i j
  | .inner leaf j k => (leafCoefficients data leaf).v j k
  | .futureMark _ _ => 0

def matrix (data : Data Y E H m t) (s : State (t+1) (m+1) ell) (leaf : Leaf (t+1)) : Y →L[ℝ] Y :=
  if leaf∈TaskState.retired s then (leafCoefficients data leaf).A else 0

def mark (data : Data Y E H m t) (s : State (t+1) (m+1) ell)
    (leaf : Leaf (t+1)) (j : Fin (m+1)) : Y :=
  if MarkSupplied s leaf j then (leafCoefficients data leaf).b j else 0

def readout (data : Data Y E H m t) (s : State (t+1) (m+1) ell)
    (leaf : Leaf (t+1)) (j : Fin (m+1)) : Y :=
  if TaskDisclosed s leaf j then (leafCoefficients data leaf).a j else 0

def completion (K : ℝ) (data : Data Y E H m t) (s : State (t+1) (m+1) ell)
    (a : Action t m) : DirectionValue E H t m a :=
  if directionDisclosed s a then direction K data a else 0

def view (K : ℝ) (data : Data Y E H m t) (s : State (t+1) (m+1) ell) : View Y E H t m ell :=
  (s,matrix data s,mark data s,readout data s,completion K data s)

theorem matrix_disclosed (data : Data Y E H m t) (s : State (t+1) (m+1) ell)
    (leaf : Leaf (t+1)) (h : leaf∈TaskState.retired s) :
    matrix data s leaf=(leafCoefficients data leaf).A := if_pos h

theorem mark_supplied (data : Data Y E H m t) (s : State (t+1) (m+1) ell)
    (leaf : Leaf (t+1)) (j : Fin (m+1)) (h : MarkSupplied s leaf j) :
    mark data s leaf j=(leafCoefficients data leaf).b j := if_pos h

theorem readout_disclosed (data : Data Y E H m t) (s : State (t+1) (m+1) ell)
    (leaf : Leaf (t+1)) (j : Fin (m+1)) (h : TaskDisclosed s leaf j) :
    readout data s leaf j=(leafCoefficients data leaf).a j := if_pos h

theorem completion_disclosed (K : ℝ) (data : Data Y E H m t) (s : State (t+1) (m+1) ell)
    (a : Action t m) (h : directionDisclosed s a) : completion K data s a=direction K data a := if_pos h

theorem view_congr (K : ℝ) (x y : Data Y E H m t) (s : State (t+1) (m+1) ell)
    (hA : ∀ leaf,leaf∈TaskState.retired s → (leafCoefficients x leaf).A=(leafCoefficients y leaf).A)
    (hb : ∀ leaf j,MarkSupplied s leaf j → (leafCoefficients x leaf).b j=(leafCoefficients y leaf).b j)
    (ha : ∀ leaf j,TaskDisclosed s leaf j → (leafCoefficients x leaf).a j=(leafCoefficients y leaf).a j)
    (hv : ∀ a,directionDisclosed s a → direction K x a=direction K y a) : view K x s=view K y s := by
  unfold view
  refine Prod.ext rfl ?_
  apply Prod.ext
  · funext leaf
    dsimp only [matrix]
    split_ifs with h
    · exact hA leaf h
    · rfl
  apply Prod.ext
  · funext leaf j
    dsimp only [mark]
    split_ifs with h
    · exact hb leaf j h
    · rfl
  apply Prod.ext
  · funext leaf j
    dsimp only [readout]
    split_ifs with h
    · exact ha leaf j h
    · rfl
  · funext a
    dsimp only [completion]
    split_ifs with h
    · exact hv a h
    · rfl

theorem retired_all_numerical (data : Data Y E H m t) (s : State (t+1) (m+1) ell)
    (leaf : Leaf (t+1)) (h : leaf∈TaskState.retired s) :
    matrix data s leaf=(leafCoefficients data leaf).A ∧
      ∀ j,mark data s leaf j=(leafCoefficients data leaf).b j ∧
        readout data s leaf j=(leafCoefficients data leaf).a j := by
  refine ⟨matrix_disclosed data s leaf h,fun j => ?_⟩
  have hj := retired_all_tasks_disclosed h j
  exact ⟨mark_supplied data s leaf j (Or.inl hj),readout_disclosed data s leaf j hj⟩

end GradientHessian.AugmentedDisclosure
