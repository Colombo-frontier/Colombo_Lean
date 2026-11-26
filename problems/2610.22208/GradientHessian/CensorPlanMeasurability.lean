import GradientHessian.ControllerCensorPlan
import GradientHessian.ControllerMeasurableTypes

/-! Finite controller plans carry the discrete sigma algebra. A total
snapshot-to-plan map returns none exactly when no current leaf remains. -/

noncomputable section
namespace GradientHessian.ControllerCensor
open Classical FrontierState TaskState ControllerMeasurable

def maskEquiv (m : ℕ) : CensoredLeaf.Mask m ≃ Fin m × Bool × (Fin m → Bool) where
  toFun q := (q.current,q.readout,q.memory)
  invFun q := ⟨q.1,q.2.1,q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance maskFintype (m : ℕ) : Fintype (CensoredLeaf.Mask m) := Fintype.ofEquiv _ (maskEquiv m).symm

def planFintype (m : ℕ) : (t : ℕ) → Fintype (CensoredHierarchy.Plan m t)
  | 0 => inferInstanceAs (Fintype (Fin 8 × (Fin 8 → Bool) × CensoredLeaf.Mask (m+1)))
  | t+1 => by
    letI := planFintype m t
    exact inferInstanceAs (Fintype (Fin 8 × (Fin 8 → Bool) × CensoredHierarchy.Plan m t))
attribute [instance] planFintype

instance planMeasurable (m t : ℕ) : MeasurableSpace (CensoredHierarchy.Plan m t) := ⊤
instance planSingleton (m t : ℕ) : MeasurableSingletonClass (CensoredHierarchy.Plan m t) := ⟨fun _ => trivial⟩

def planOption {t m ell : ℕ} (before after : State (t+1) (m+1) ell) : Option (CensoredHierarchy.Plan m t) :=
  match hc : TaskState.current before with
  | none => none
  | some leaf => some (planAt before after leaf hc t)

theorem planOption_measurable (t m ell : ℕ) :
    Measurable (fun q : State (t+1) (m+1) ell × State (t+1) (m+1) ell => planOption q.1 q.2) :=
  measurable_of_countable _

theorem planAt_measurable {t m ell : ℕ} (leaf : Leaf (t+1)) :
    Measurable (fun q : {s : State (t+1) (m+1) ell // TaskState.current s=some leaf} × State (t+1) (m+1) ell =>
      planAt q.1.1 q.2 leaf q.1.2 t) := measurable_of_countable _

theorem planOption_current {t m ell : ℕ} (before after : State (t+1) (m+1) ell) (leaf : Leaf (t+1))
    (hc : TaskState.current before=some leaf) : planOption before after=some (planAt before after leaf hc t) := by
  unfold planOption
  split
  · rename_i hn
    simp [hc] at hn
  · rename_i other he
    have h : other=leaf := Option.some.inj (he.symm.trans hc)
    subst other
    rfl

end GradientHessian.ControllerCensor
