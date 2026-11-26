import Bilevel.ChiNodeNewColumnForce

/-! Exact pre-wrapper forces for the actual closed joint carriers, including
their actual child release values and all ancestor selectors. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def actualReleases (m : ℕ) (D : Geometry E) (j : ℕ) (I : List ℕ) (x : Blocks m E) : Fin ((D j I).n+1) → ℝ :=
  fun i => (D (j+1) (child I i.val)).release (block m (j+1) x)

def closedJointForce (m : ℕ) (D : Geometry E) (j : ℕ) (I : List ℕ) (x : Blocks m E) : E :=
  (D j I).latentForce (closedCarrier (D j I).n (D j I).ell (D j I).width (D j I).receiver
    (D j I).nu (D j I).force (D j I).parentWidth (D j I).tailRadius (actualReleases m D j I x)) (block m j x)

theorem jointClosed_block_gradient {m : ℕ} (D : Geometry E) (d j : ℕ) (I : List ℕ)
    (hj : j<m) (hR : 0<(D j I).radius) (x : Blocks m E) :
    (gradient (jointCarrier m D (d+1) j I 0) x) ⟨j,hj⟩=
      RadialWrapper.compressDerivative (D j I).radius (x ⟨j,hj⟩) (closedJointForce m D j I x) := by
  rw [← gradient_replaceBlock x ⟨j,hj⟩ ((jointCarrier_contDiff m D (d+1) j I 0 3).differentiable (by norm_num) x)]
  have he : (fun v => jointCarrier m D (d+1) j I 0 (replaceBlock x ⟨j,hj⟩ v))=
      (D j I).closed (actualReleases m D j I x) := by
    funext v
    simp only [jointCarrier,selectedCarrier,padded,Node.closed,actualReleases,block_replaceBlock,
      if_pos rfl,if_true,if_neg (by omega : j+1≠j)]
  rw [he,Node.closed_formula]
  rw [(D j I).carried_gradient_latentForce _ (closedCarrier_contDiff _ _ _ _ _ _ _ _ _) hR]
  simp only [closedJointForce,block,dif_pos hj,PiLp.proj_apply]

theorem closedJointForce_new_column_zero {m : ℕ} (D : Geometry E) (j : ℕ) (I : List ℕ)
    (r : ℕ) (hh : 0<(D j I).width) (x : Blocks m E)
    (hp : ∀ i : Fin ((D j I).n+1),0<(D (j+1) (child I i.val)).parentWidth)
    (hw : ∀ i : Fin ((D j I).n+1),(D (j+1) (child I i.val)).width≤(D (j+1) (child I i.val)).parentWidth)
    (hchild : ∀ i : Fin ((D j I).n+1),r ≤ i.val →
      |(D (j+1) (child I i.val)).coordinates (block m (j+1) x) (Fin.last (D (j+1) (child I i.val)).n)|≤
        (D (j+1) (child I i.val)).width/4)
    (hz : ∀ k : Fin ((D j I).n+1),r≤k.val → |(D j I).coordinates (block m j x) k|≤(D j I).width/4)
    (k : Fin ((D j I).n+1)) (hk : r≤k.val) :
    ⟪(D j I).frame (basis k),closedJointForce m D j I x⟫=0 := by
  exact (D j I).actual_child_closed_new_force_zero r hh (fun i => D (j+1) (child I i.val))
    (fun _ => block m (j+1) x) hp hw hchild (block m j x) hz k hk

def selectedClosedForce (m : ℕ) (D : Geometry E) (t j : ℕ) (I : List ℕ) (x : Blocks m E) : E :=
  selectVectors m D (fun k P y => closedJointForce m D k P y) t j I x

theorem selectedClosed_block_gradient {m : ℕ} (D : Geometry E) (d t j : ℕ) (I : List ℕ)
    (hm : j+t<m) (R : ℝ) (hR : 0<R) (hRnode : ∀ P,(D (j+t) P).radius=R) (x : Blocks m E) :
    (gradient (jointCarrier m D (d+1+t) j I t) x) ⟨j+t,hm⟩=
      RadialWrapper.compressDerivative R (x ⟨j+t,hm⟩) (selectedClosedForce m D t j I x) := by
  rw [jointCarrier_selectFamily,selected_gradient_terminal_block D _
    (fun k P => jointCarrier_contDiff m D (d+1) k P 0 3) t j I ⟨j+t,hm⟩ rfl]
  unfold selectedClosedForce
  rw [← selectVectors_map]
  apply selectVectors_congr_leaf
  intro P
  rw [jointClosed_block_gradient D d (j+t) P hm (by rw [hRnode];exact hR),hRnode]

end Bilevel.ChiCarrier
