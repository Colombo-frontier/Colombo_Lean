import GradientHessian.GeometricDisclosure
import GradientHessian.FirstHeightScales
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Finset.Sort

/-! The finite public action inventory and exact retirement targets. The
last localized child targets its whole parent; old memory hits target the
whole height-one node. All addresses index data, never physical coordinates. -/

noncomputable section
namespace GradientHessian.GeometricRepair
open Classical FrontierState

inductive Action (t m : ℕ) where
  | localized (h : Fin t) (path : Fin (t-(h.val+1)) → Fin 8) (i : Fin 8)
  | old (path : Fin t → Fin 8) (i : Fin 8) (j : Fin (FirstHeight.depth (m+1)+2))
  | inner (leaf : Leaf (t+1)) (task : Fin (m+1)) (j : Fin (Inner.absoluteDepth+2))
  | futureMark (leaf : Leaf (t+1)) (task : Fin (m+1))
  deriving Fintype, DecidableEq

variable {t m : ℕ}

def localNode (h : Fin t) (path : Fin (t-(h.val+1)) → Fin 8) : Node (t+1) :=
  ⟨⟨t-(h.val+1), by omega⟩,path⟩

def oldNode (path : Fin t → Fin 8) : Node (t+1) := ⟨⟨t,by omega⟩,path⟩

theorem localNode_internal (h : Fin t) (path : Fin (t-(h.val+1)) → Fin 8) :
    (localNode h path).1.val<t+1 := by simp [localNode]; omega

theorem oldNode_internal (path : Fin t → Fin 8) : (oldNode path).1.val<t+1 := by
  simp [oldNode]

def localChild (h : Fin t) (path : Fin (t-(h.val+1)) → Fin 8) (i : Fin 8) : Node (t+1) :=
  child (localNode h path) (localNode_internal h path) i

def oldChild (path : Fin t → Fin 8) (i : Fin 8) : Node (t+1) :=
  child (oldNode path) (oldNode_internal path) i

def target : Action t m → Node (t+1)
  | .localized h path i => if i=Fin.last 7 then localNode h path else localChild h path i
  | .old path _ _ => oldNode path
  | .inner leaf _ _ | .futureMark leaf _ => leafNode leaf

@[simp] theorem target_localized_last (h : Fin t) (path : Fin (t-(h.val+1)) → Fin 8) :
    target (.localized h path (Fin.last 7) : Action t m) = localNode h path := by simp [target]

theorem localChild_subset_target (h : Fin t) (path : Fin (t-(h.val+1)) → Fin 8) (i : Fin 8) :
    subtree (localChild h path i) ⊆ subtree (target (.localized h path i : Action t m)) := by
  by_cases hi : i=Fin.last 7
  · simp only [target,hi,ite_true]
    exact subtree_child_subset _ _ _
  · simp only [target,if_neg hi]
    exact Finset.Subset.refl _

/-- Public priority: ancestors first, then child/task, register, rule kind,
and a fixed finite-index tie breaker among distinct addresses. -/
def priorityKey (a : Action t m) : Lex (Fin 5 → ℕ) := toLex <| match a with
  | .localized h _ i => ![t-(h.val+1),i.val,0,0,(Fintype.equivFin (Action t m) a).val]
  | .old _ i j => ![t,i.val,j.val,1,(Fintype.equivFin (Action t m) a).val]
  | .inner _ task j => ![t+1,task.val,j.val,2,(Fintype.equivFin (Action t m) a).val]
  | .futureMark _ task => ![t+1,task.val,0,3,(Fintype.equivFin (Action t m) a).val]

theorem priorityKey_injective : Function.Injective (priorityKey : Action t m → _) := by
  intro a b hab
  have he := congrArg (fun k : Lex (Fin 5 → ℕ) => k 4) hab
  have hv (c : Action t m) : priorityKey c 4 = (Fintype.equivFin (Action t m) c).val := by
    cases c <;> rfl
  change priorityKey a 4 = priorityKey b 4 at he
  rw [hv,hv] at he
  exact (Fintype.equivFin (Action t m)).injective (Fin.ext he)

instance actionOrder : LinearOrder (Action t m) := LinearOrder.lift' priorityKey priorityKey_injective

def priority (t m : ℕ) : List (Action t m) := Finset.univ.sort (·≤·)

@[simp] theorem mem_priority (a : Action t m) : a ∈ priority t m := by
  simp [priority]

theorem priority_nodup (t m : ℕ) : (priority t m).Nodup := Finset.sort_nodup _ _

end GradientHessian.GeometricRepair
