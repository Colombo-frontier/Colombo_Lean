import Bilevel.ChiRecursiveNodeDerivative

/-! Exact differentiation of the constructed recursive objective in one
block, and reduction of its perturbation to the actual unique active child. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiRecursive
open ChiBoundedChain RadialWrapper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def Node.localBase (D : Node E) (ρ w Rp : ℝ) : E → ℝ :=
  weightedLocal D.n D.ell D.width D.receiver D.nu D.force D.parentWidth D.tailRadius
    w Rp ρ D.radius D.frame

theorem Node.localBase_formula (D : Node E) (ρ w Rp : ℝ) (v : E) :
    D.localBase ρ w Rp v=bowl ρ D.radius v+w*D.H v+Rp*D.release v :=
  weightedLocal_formula _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem Node.localBase_differentiable (D : Node E) (hR : 0<D.radius) (ρ w Rp : ℝ) :
    Differentiable ℝ (D.localBase ρ w Rp) := fun v =>
  (weightedLocal_hasGradientAt D.n D.ell D.width D.receiver D.nu D.force D.parentWidth D.tailRadius
    w Rp ρ D.radius hR D.frame v).differentiableAt

def sliceObjective (D : Geometry E) (d j : ℕ) (I : List ℕ) (u : ℕ → E)
    (ρ w Rp : ℝ) (v : E) : ℝ :=
  bowl ρ (D j I).radius v+w*payloadValue D d j I (Function.update u j v)+Rp*(D j I).release v

def correction (D : Geometry E) (d j : ℕ) (I : List ℕ) (u : ℕ → E) (v : E) : ℝ :=
  ∑ i : Fin ((D j I).n+1),
    (((D (j+1) (child I i.val)).release (u (j+1))-1)*(D j I).residual i v+
    payloadValue D d (j+1) (child I i.val) u*(D j I).selector i v)

def perturbation (D : Geometry E) (d j : ℕ) (I : List ℕ) (u : ℕ → E) (v : E) : E →L[ℝ] ℝ :=
  ∑ i : Fin ((D j I).n+1),
    (((D (j+1) (child I i.val)).release (u (j+1))-1) • fderiv ℝ ((D j I).residual i) v+
    payloadValue D d (j+1) (child I i.val) u • fderiv ℝ ((D j I).selector i) v)

theorem sliceObjective_succ (D : Geometry E) (d j : ℕ) (I : List ℕ) (u : ℕ → E)
    (ρ w Rp : ℝ) :
    sliceObjective D (d+1) j I u ρ w Rp=
      fun v => (D j I).localBase ρ w Rp v+w*correction D d j I u v := by
  funext v
  rw [sliceObjective,payloadValue_update_current,Node.localBase_formula]
  simp only [correction,Finset.sum_add_distrib,sub_mul,Finset.sum_sub_distrib,one_mul]
  have hr : (∑ i : Fin ((D j I).n+1),
      (D (j+1) (child I i.val)).release (u (j+1))*(D j I).residual i v)=
      ∑ i : Fin ((D j I).n+1),(D j I).residual i v*(D (j+1) (child I i.val)).release (u (j+1)) := by
    apply Finset.sum_congr rfl
    intros
    ring
  have hw : (∑ i : Fin ((D j I).n+1),payloadValue D d (j+1) (child I i.val) u*(D j I).selector i v)=
      ∑ i : Fin ((D j I).n+1),(D j I).selector i v*payloadValue D d (j+1) (child I i.val) u := by
    apply Finset.sum_congr rfl
    intros
    ring
  rw [hr,hw]
  ring

theorem correction_hasFDerivAt (D : Geometry E) (d j : ℕ) (I : List ℕ) (u : ℕ → E) (v : E) :
    HasFDerivAt (correction D d j I u) (perturbation D d j I u v) v := by
  unfold correction perturbation
  apply HasFDerivAt.sum
  intro i _
  exact ((((D j I).residual_contDiff i 1).differentiable (by norm_num) v).hasFDerivAt.const_mul _).add
    ((((D j I).selector_contDiff i 1).differentiable (by norm_num) v).hasFDerivAt.const_mul _)

/-- The actual derivative is the weighted local base plus the source
one-child perturbation; this equality is derived from the recursive formula. -/
theorem sliceObjective_succ_fderiv (D : Geometry E) (d j : ℕ) (I : List ℕ) (u : ℕ → E)
    (hR : 0<(D j I).radius) (ρ w Rp : ℝ) (v : E) :
    fderiv ℝ (sliceObjective D (d+1) j I u ρ w Rp) v=
      fderiv ℝ ((D j I).localBase ρ w Rp) v+w • perturbation D d j I u v := by
  rw [sliceObjective_succ]
  exact (((D j I).localBase_differentiable hR ρ w Rp v).hasFDerivAt.add
    ((correction_hasFDerivAt D d j I u v).const_mul w)).fderiv

theorem sliceObjective_leaf_fderiv (D : Geometry E) (j : ℕ) (I : List ℕ) (u : ℕ → E)
    (hR : 0<(D j I).radius) (ρ w Rp : ℝ) (v : E) :
    fderiv ℝ (sliceObjective D 0 j I u ρ w Rp) v=
      fderiv ℝ ((D j I).localBase ρ w Rp) v := by
  have he : sliceObjective D 0 j I u ρ w Rp=
      fun t => (D j I).localBase ρ w Rp t-w*(D j I).H 0 := by
    funext t
    simp only [sliceObjective,payloadValue,Function.update_self,Node.localBase_formula]
    ring
  rw [he]
  exact (((D j I).localBase_differentiable hR ρ w Rp v).hasFDerivAt.sub_const _).fderiv

theorem Node.selector_fderiv_zero (D : Node E) (i : Fin (D.n+1)) (v : E)
    (hi : D.selector i v=0) : fderiv ℝ (D.selector i) v=0 := by
  have hm : IsLocalMin (D.selector i) v := by
    apply Filter.Eventually.of_forall
    intro t
    rw [hi]
    exact (D.selector_range i t).1
  exact hm.hasFDerivAt_eq_zero (((D.selector_contDiff i 1).differentiable (by norm_num) v).hasFDerivAt)

theorem Node.residual_fderiv_zero (D : Node E) (i : Fin (D.n+1)) (v : E)
    (hi : D.selector i v=0) : fderiv ℝ (D.residual i) v=0 := by
  have hs : ChiBoundedChain.selector D.n i (D.width⁻¹ • D.coordinates v)=0 := hi
  rw [(D.residual_hasFDerivAt i v).fderiv]
  simp [residualTermDerivative,selectorDerivative_zero_of_zero i _ hs,hs]

theorem perturbation_eq_active (D : Geometry E) (d j : ℕ) (I : List ℕ) (u : ℕ → E) (v : E)
    (i : Fin ((D j I).n+1)) (hi : (D j I).selector i v≠0) :
    perturbation D d j I u v=
      ((D (j+1) (child I i.val)).release (u (j+1))-1) • fderiv ℝ ((D j I).residual i) v+
      payloadValue D d (j+1) (child I i.val) u • fderiv ℝ ((D j I).selector i) v := by
  unfold perturbation
  apply Finset.sum_eq_single i
  · intro k _ hki
    have hk : (D j I).selector k v=0 := by
      by_contra hk
      exact hki ((D j I).selector_unique k i v hk hi)
    rw [Node.residual_fderiv_zero _ _ _ hk,Node.selector_fderiv_zero _ _ _ hk]
    simp
  · simp

theorem perturbation_zero_of_inactive (D : Geometry E) (d j : ℕ) (I : List ℕ) (u : ℕ → E) (v : E)
    (hi : ∀ i : Fin ((D j I).n+1),(D j I).selector i v=0) : perturbation D d j I u v=0 := by
  unfold perturbation
  apply Finset.sum_eq_zero
  intro i _
  rw [Node.residual_fderiv_zero _ _ _ (hi i),Node.selector_fderiv_zero _ _ _ (hi i)]
  simp

end Bilevel.ChiRecursive
