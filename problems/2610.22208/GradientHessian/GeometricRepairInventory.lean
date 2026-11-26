import GradientHessian.GeometricRepairRules
import GradientHessian.ControllerRepairEvents
import Mathlib.Algebra.BigOperators.Fin

/-! Exact finite inventory and retirement cost of the literal geometric
repair actions. The last localized child retires its whole parent. -/

noncomputable section
namespace GradientHessian.GeometricRepair
open Classical FrontierState ControllerRepairEvents
open scoped BigOperators

abbrev LocalIndex (t : ℕ) := (h : Fin t) × ((Fin (t-(h.val+1)) → Fin 8) × Fin 8)
abbrev OldIndex (t m : ℕ) := (Fin t → Fin 8) × Fin 8 × Fin (FirstHeight.depth (m+1)+2)
abbrev InnerIndex (t m : ℕ) := Leaf (t+1) × Fin (m+1) × Fin (Inner.absoluteDepth+2)
abbrev MarkIndex (t m : ℕ) := Leaf (t+1) × Fin (m+1)

def inventoryEquiv (t m : ℕ) : Action t m ≃
    LocalIndex t ⊕ OldIndex t m ⊕ InnerIndex t m ⊕ MarkIndex t m where
  toFun a := match a with
    | .localized h path i => .inl ⟨h,path,i⟩
    | .old path i j => .inr (.inl (path,i,j))
    | .inner leaf task j => .inr (.inr (.inl (leaf,task,j)))
    | .futureMark leaf task => .inr (.inr (.inr (leaf,task)))
  invFun a := match a with
    | .inl ⟨h,path,i⟩ => .localized h path i
    | .inr (.inl (path,i,j)) => .old path i j
    | .inr (.inr (.inl (leaf,task,j))) => .inner leaf task j
    | .inr (.inr (.inr (leaf,task))) => .futureMark leaf task
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with a|a|a|a <;> rfl

theorem action_sum {V : Type*} [AddCommMonoid V] (t m : ℕ) (f : Action t m → V) :
    (∑ a, f a) =
      (∑ h : Fin t, ∑ path : Fin (t-(h.val+1)) → Fin 8, ∑ i, f (.localized h path i)) +
      (∑ path : Fin t → Fin 8, ∑ i, ∑ j, f (.old path i j)) +
      (∑ leaf : Leaf (t+1), ∑ task, ∑ j, f (.inner leaf task j)) +
      (∑ leaf : Leaf (t+1), ∑ task, f (.futureMark leaf task)) := by
  have he := (inventoryEquiv t m).sum_comp (fun a => f ((inventoryEquiv t m).symm a))
  simpa only [Equiv.symm_apply_apply,Fintype.sum_sum_type,Fintype.sum_sigma,
    Fintype.sum_prod_type,inventoryEquiv,Equiv.coe_fn_symm_mk,add_assoc] using he

theorem action_card (t m : ℕ) :
    Fintype.card (Action t m) =
      (∑ h : Fin t, 8^(t-(h.val+1))*8) +
        8^t*8*(FirstHeight.depth (m+1)+2) +
        8^(t+1)*(m+1)*(Inner.absoluteDepth+2) + 8^(t+1)*(m+1) := by
  simpa [leaf_card,Nat.mul_assoc] using action_sum t m (fun _ => (1:ℕ))

def publicCost {t m : ℕ} (a : Action t m) : ℕ := (subtree (target a)).card*(m+1)

theorem publicCost_localized {t m : ℕ} (h : Fin t)
    (path : Fin (t-(h.val+1)) → Fin 8) (i : Fin 8) :
    publicCost (.localized h path i : Action t m) =
      (if i=Fin.last 7 then 8^(h.val+2) else 8^(h.val+1))*(m+1) := by
  by_cases hi : i=Fin.last 7
  · simp only [publicCost,target,hi,if_true,subtree_card,localNode]
    congr 2
    omega
  · simp only [publicCost,target,if_neg hi,subtree_card,localChild,child,localNode]
    congr 2
    omega

@[simp] theorem publicCost_old {t m : ℕ} (path : Fin t → Fin 8) (i : Fin 8)
    (j : Fin (FirstHeight.depth (m+1)+2)) :
    publicCost (.old path i j : Action t m) = 8*(m+1) := by
  simp [publicCost,target,subtree_card,oldNode]

@[simp] theorem publicCost_inner {t m : ℕ} (leaf : Leaf (t+1)) (task : Fin (m+1))
    (j : Fin (Inner.absoluteDepth+2)) : publicCost (.inner leaf task j : Action t m) = m+1 := by
  simp [publicCost,target]

@[simp] theorem publicCost_mark {t m : ℕ} (leaf : Leaf (t+1)) (task : Fin (m+1)) :
    publicCost (.futureMark leaf task : Action t m) = m+1 := by simp [publicCost,target]

theorem local_cost_sum {t m : ℕ} (h : Fin t) (path : Fin (t-(h.val+1)) → Fin 8) :
    (∑ i, publicCost (.localized h path i : Action t m)) = 15*8^(h.val+1)*(m+1) := by
  simp_rw [publicCost_localized]
  rw [Fin.sum_univ_castSucc]
  have hn (i : Fin 7) : i.castSucc ≠ Fin.last 7 := Fin.castSucc_ne_last i
  simp only [hn,if_false,if_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [show h.val+2=(h.val+1)+1 by omega,pow_succ]
  ring

def familyBound {t m : ℕ} (loc : Fin t → ℝ) (old inner mark : ℝ) : Action t m → ℝ
  | .localized h _ _ => loc h
  | .old _ _ _ => old
  | .inner _ _ _ => inner
  | .futureMark _ _ => mark

theorem family_cost_sum (t m : ℕ) (loc : Fin t → ℝ) (old inner mark : ℝ) :
    (∑ a : Action t m, (publicCost a:ℝ)*familyBound loc old inner mark a) =
      (8:ℝ)^(t+1)*(m+1)*((15/8:ℝ)*(∑ h, loc h) +
        8*(FirstHeight.depth (m+1)+2)*old +
        (m+1)*(Inner.absoluteDepth+2)*inner + (m+1)*mark) := by
  rw [action_sum]
  simp only [familyBound,publicCost_old,publicCost_inner,publicCost_mark]
  have hloc (h : Fin t) :
      (∑ path : Fin (t-(h.val+1)) → Fin 8,
        ∑ i, (publicCost (.localized h path i : Action t m):ℝ)*loc h) =
      (15:ℝ)*8^t*(m+1)*loc h := by
    simp_rw [← Finset.sum_mul,← Nat.cast_sum,local_cost_sum]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
      nsmul_eq_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
    have hp : (8:ℝ)^(t-(h.val+1))*8^(h.val+1)=8^t := by
      rw [← pow_add,Nat.sub_add_cancel (Nat.succ_le_of_lt h.isLt)]
    rw [← hp]
    ring
  simp_rw [hloc]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
    leaf_card,nsmul_eq_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
  rw [← Finset.mul_sum]
  simp only [pow_succ]
  ring

end GradientHessian.GeometricRepair
