import Bilevel.ChiRecursiveSlice

/-! The recursive objective with every public radial penalty outside every
selector, and exact block-derivative transport along the unique active path. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiRecursive
open ChiBoundedChain RadialWrapper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def publicValue (ρ R : ℕ → ℝ) : ℕ → ℕ → (ℕ → E) → ℝ
  | 0,j,u => bowl (ρ j) (R j) (u j)
  | d+1,j,u => bowl (ρ j) (R j) (u j)+publicValue ρ R d (j+1) u

def objective (D : Geometry E) (ρ R : ℕ → ℝ) (d j : ℕ) (I : List ℕ)
    (w Rp : ℝ) (u : ℕ → E) : ℝ :=
  publicValue ρ R d j u+w*payloadValue D d j I u+Rp*(D j I).release (u j)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem publicValue_update_earlier (ρ R : ℕ → ℝ) (d j k : ℕ) (u : ℕ → E)
    (v : E) (hkj : k<j) : publicValue ρ R d j (Function.update u k v)=publicValue ρ R d j u := by
  induction d generalizing j with
  | zero => simp only [publicValue,Function.update_of_ne (by omega : j≠k)]
  | succ d ih =>
    simp only [publicValue,Function.update_of_ne (by omega : j≠k),ih (j+1) (by omega)]

theorem objective_own_block_derivative (D : Geometry E) (ρ R : ℕ → ℝ) (d j : ℕ) (I : List ℕ)
    (w Rp : ℝ) (u : ℕ → E) (hR : R j=(D j I).radius) (v : E) :
    fderiv ℝ (fun t => objective D ρ R d j I w Rp (Function.update u j t)) v=
      fderiv ℝ (sliceObjective D d j I u (ρ j) w Rp) v := by
  cases d with
  | zero =>
    congr 1
    funext t
    simp only [objective,publicValue,Function.update_self,hR,sliceObjective]
  | succ d =>
    have he : (fun t => objective D ρ R (d+1) j I w Rp (Function.update u j t))=
        fun t => sliceObjective D (d+1) j I u (ρ j) w Rp t+publicValue ρ R d (j+1) u := by
      funext t
      simp only [objective,publicValue,Function.update_self,hR,sliceObjective,
        publicValue_update_earlier ρ R d (j+1) j u t (by omega)]
      ring
    rw [he,fderiv_add_const]

theorem Node.residual_zero_of_selector_zero (D : Node E) (i : Fin (D.n+1)) (v : E)
    (hi : D.selector i v=0) : D.residual i v=0 := by
  have hs : ChiBoundedChain.selector D.n i (D.width⁻¹ • D.coordinates v)=0 := hi
  simp only [Node.residual,Rterm_formula,hs,mul_zero,zero_mul]

theorem payloadValue_future_active (D : Geometry E) (d j k : ℕ) (I : List ℕ) (u : ℕ → E)
    (v : E) (hjk : j<k) (i : Fin ((D j I).n+1)) (hi : (D j I).selector i (u j)≠0) :
    payloadValue D (d+1) j I (Function.update u k v)=
      (D j I).H (u j)-(D j I).residual i (u j)+
      (D j I).residual i (u j)*(D (j+1) (child I i.val)).release ((Function.update u k v) (j+1))+
      (D j I).selector i (u j)*payloadValue D d (j+1) (child I i.val) (Function.update u k v) := by
  have hzero : ∀ a : Fin ((D j I).n+1),a≠i → (D j I).selector a (u j)=0 := by
    intro a hai
    by_contra ha
    exact hai ((D j I).selector_unique a i (u j) ha hi)
  have hres : ∀ a : Fin ((D j I).n+1),a≠i → (D j I).residual a (u j)=0 :=
    fun a hai => (D j I).residual_zero_of_selector_zero a (u j) (hzero a hai)
  have hr : (∑ a : Fin ((D j I).n+1),(D j I).residual a (u j))=(D j I).residual i (u j) := by
    apply Finset.sum_eq_single i
    · intro a _ hai
      exact hres a hai
    · simp
  have hrq : (∑ a : Fin ((D j I).n+1),(D j I).residual a (u j)*
      (D (j+1) (child I a.val)).release ((Function.update u k v) (j+1)))=
      (D j I).residual i (u j)*(D (j+1) (child I i.val)).release ((Function.update u k v) (j+1)) := by
    apply Finset.sum_eq_single i
    · intro a _ hai
      rw [hres a hai,zero_mul]
    · simp
  have hw : (∑ a : Fin ((D j I).n+1),(D j I).selector a (u j)*
      payloadValue D d (j+1) (child I a.val) (Function.update u k v))=
      (D j I).selector i (u j)*payloadValue D d (j+1) (child I i.val) (Function.update u k v) := by
    apply Finset.sum_eq_single i
    · intro a _ hai
      rw [hzero a hai,zero_mul]
    · simp
  simp only [payloadValue,Function.update_of_ne (by omega : j≠k),hr,hrq,hw]

/-- Exact equality up to a constant when descending to the selected child. -/
theorem objective_future_active (D : Geometry E) (ρ R : ℕ → ℝ) (d j k : ℕ) (I : List ℕ)
    (w Rp : ℝ) (u : ℕ → E) (hjk : j<k)
    (i : Fin ((D j I).n+1)) (hi : (D j I).selector i (u j)≠0) :
    (fun v => objective D ρ R (d+1) j I w Rp (Function.update u k v))=
      fun v => (bowl (ρ j) (R j) (u j)+w*((D j I).H (u j)-(D j I).residual i (u j))+
        Rp*(D j I).release (u j))+
        objective D ρ R d (j+1) (child I i.val) (w*(D j I).selector i (u j))
          (w*(D j I).residual i (u j)) (Function.update u k v) := by
  funext v
  unfold objective
  rw [payloadValue_future_active D d j k I u v hjk i hi]
  simp only [publicValue,Function.update_of_ne (by omega : j≠k)]
  ring

theorem objective_descendant_derivative (D : Geometry E) (ρ R : ℕ → ℝ) (d j k : ℕ) (I : List ℕ)
    (w Rp : ℝ) (u : ℕ → E) (hjk : j<k)
    (i : Fin ((D j I).n+1)) (hi : (D j I).selector i (u j)≠0) (v : E) :
    fderiv ℝ (fun t => objective D ρ R (d+1) j I w Rp (Function.update u k t)) v=
      fderiv ℝ (fun t => objective D ρ R d (j+1) (child I i.val)
        (w*(D j I).selector i (u j)) (w*(D j I).residual i (u j)) (Function.update u k t)) v := by
  rw [objective_future_active D ρ R d j k I w Rp u hjk i hi,fderiv_const_add]

end Bilevel.ChiRecursive
