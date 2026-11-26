import Bilevel.ChiTreeSingleRelease
import Bilevel.ChiTreeProgressUpdate

/-! The source hierarchy starts below a macro coordinate. Its actual prefix
lists have length j+1. This adapter uses one global success counter including
the macro branching factor, and discharges the future-child and single
unfinished-frontier requirements of the nonlinear support theorem. -/
noncomputable section
namespace Bilevel.ChiTreeProgress
open ChiCarrier ChiRecursive ChiBoundedChain

theorem capacity_shift (n : ℕ → ℕ) (d j a : ℕ) :
    capacity (fun k => n (k+a)) d j=capacity n d (j+a) := by
  induction d generalizing j with
  | zero => rfl
  | succ d ih => simp only [capacity,ih];congr 2;omega

theorem nodePrefix_shift (n : ℕ → ℕ) (d j q a : ℕ) :
    nodePrefix (fun k => n (k+a)) d j q=nodePrefix n d (j+a) q := by
  cases d with
  | zero => rfl
  | succ d => simp only [nodePrefix,capacity_shift];congr 2;omega

def innerCounter (n : ℕ → ℕ) (J q j : ℕ) (I : List ℕ) : ℕ :=
  counter n (J+1) q (j+1) I

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem inner_budgetTree (D : Geometry E) (n : ℕ → ℕ)
    (hn : ∀ j I,(D j I).n=n (j+1)) (J q d j : ℕ) (I : List ℕ)
    (hI : I.length=j+1) (hd : j+d=J) :
    BudgetTree D (fun k => n (k+1)) (innerCounter n J q) d j I
      (nodeBudget n (J+1) 0 q I) := by
  induction d generalizing j I with
  | zero =>
    refine ⟨hn j I,?_⟩
    rw [innerCounter,counter_at n (J+1) q (j+1) I hI,nodePrefix_shift]
    congr 1;omega
  | succ d ih =>
    refine ⟨hn j I,?_,?_⟩
    · rw [innerCounter,counter_at n (J+1) q (j+1) I hI,nodePrefix_shift]
      congr 1;omega
    · intro i
      have hIc : (child I i.val).length=(j+1)+1 := by simp [child,hI]
      have hi := ih (j+1) (child I i.val) hIc (by omega)
      have he : J+1-((j+1)+1)=d := by omega
      simpa only [child,counter_child_budget n (J+1) q (j+1) I hI,he,capacity_shift] using hi

theorem inner_future (D : Geometry E) (n : ℕ → ℕ)
    (hn : ∀ j I,(D j I).n=n (j+1)) (J q t : ℕ) (ht : t<J) (P : List ℕ)
    (i : Fin ((D t P).n+1)) (hi : innerCounter n J q t P ≤ i.val) :
    innerCounter n J q (t+1) (child P i.val)≤(D (t+1) (child P i.val)).n := by
  have hif : i.val<n (t+1)+1 := by rw [←hn t P];exact i.isLt
  rw [hn (t+1) (child P i.val)]
  exact counter_future n (J+1) q (t+1) P (by omega) ⟨i.val,hif⟩ hi

theorem inner_single_release (D : Geometry E) (n : ℕ → ℕ)
    (hn : ∀ j I,(D j I).n=n (j+1)) (J q macroIndex : ℕ) (V : Submodule ℝ E) :
    FrontierKnown D (innerCounter n J q)
      (enlargedSpace V (nextRelease D (innerCounter n J q) J 0 [macroIndex])) J 0 [macroIndex] :=
  (inner_budgetTree D n hn J q J 0 [macroIndex] rfl (by omega)).frontier _
    (enlargedSpace_contains_release V _)

theorem inner_counter_success_bounds (n : ℕ → ℕ) (J q j : ℕ) (I : List ℕ) :
    innerCounter n J q j I ≤ innerCounter n J (q+1) j I ∧
      innerCounter n J (q+1) j I ≤ innerCounter n J q j I+1 :=
  counter_success_bounds n (J+1) q (j+1) I

theorem inner_changed_path_unique (n : ℕ → ℕ) (J q j : ℕ) (I K : List ℕ)
    (hIlen : I.length=j+1) (hKlen : K.length=j+1)
    (hI : innerCounter n J (q+1) j I≠innerCounter n J q j I)
    (hK : innerCounter n J (q+1) j K≠innerCounter n J q j K) : I=K :=
  counter_changed_path_unique n (J+1) q (j+1) I K hIlen hKlen hI hK

end Bilevel.ChiTreeProgress
