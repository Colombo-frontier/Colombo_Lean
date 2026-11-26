import Bilevel.ChiCarrierReleaseLocality

/-! Full joint support of the actual closed recursive carrier. This uses
the exact signed cancellation at the parent and differentiates every child
release; it is stronger than checking only the own-block derivative. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive

section Algebra
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem gradient_sub_const_mem (W : Submodule ℝ F) {f : F → ℝ} (hf : ContDiff ℝ 3 f)
    (x : F) (c : ℝ) (hm : gradient f x∈W) : gradient (fun y => f y-c) x∈W := by
  have hd := ((hf.differentiable (by norm_num) x).hasGradientAt.hasFDerivAt).sub_const c
  have hh : HasGradientAt (fun y => f y-c) (gradient f x) x := hd
  rw [hh.gradient]
  exact hm

theorem gradient_mul_mem_of_right_zero (W : Submodule ℝ F) {f g : F → ℝ}
    (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x : F)
    (hgzero : g x=0) (hgm : gradient g x∈W) : gradient (fun y => f y*g y) x∈W := by
  have hd := ((hf.differentiable (by norm_num) x).hasGradientAt.hasFDerivAt).mul
    ((hg.differentiable (by norm_num) x).hasGradientAt.hasFDerivAt)
  have hh : HasGradientAt (fun y => f y*g y) (f x • gradient g x) x := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    simpa only [hgzero,zero_smul,add_zero,map_smul] using hd
  rw [hh.gradient]
  exact W.smul_mem _ hgm
end Algebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem jointClosed_gradient_mem {m : ℕ} (D : Geometry E) (d j : ℕ) (I : List ℕ)
    (hm : j+1 < m) (W : Fin m → Submodule ℝ E) (x : Blocks m E) (r : ℕ)
    (hparent : BlindNode W x ⟨j,by omega⟩ (D j I) r)
    (rc : Fin ((D j I).n+1) → ℕ)
    (hchild : ∀ i,BlindNode W x ⟨j+1,hm⟩ (D (j+1) (child I i.val)) (rc i))
    (hhp : ∀ i : Fin ((D j I).n+1),0<(D (j+1) (child I i.val)).parentWidth)
    (hw : ∀ i : Fin ((D j I).n+1),(D (j+1) (child I i.val)).width≤
      (D (j+1) (child I i.val)).parentWidth)
    (hfuture : ∀ i : Fin ((D j I).n+1),r ≤ i.val → rc i≤(D (j+1) (child I i.val)).n) :
    gradient (jointCarrier m D (d+1) j I 0) x∈knownSpace W := by
  let q : Fin ((D j I).n+1) → ℝ := fun i => (D (j+1) (child I i.val)).release (x ⟨j+1,hm⟩)
  have hq : ∀ i : Fin ((D j I).n+1),r ≤ i.val → q i=0 := by
    intro i hi
    exact ((D (j+1) (child I i.val)).release_flat_of_blind_terminal (hhp i) (hw i) _
      ((hchild i).blind (Fin.last _) (by simpa using hfuture i hi))).1
  have hclosed : ContDiff ℝ 3 ((D j I).closed q) := by
    rw [Node.closed_formula]
    exact (closedCarrier_contDiff _ _ _ _ _ _ _ _ q).comp ((D j I).coordinates_contDiff 3)
  have hcjoint := hclosed.comp (block (E:=E) m j).contDiff
  have hcmem : gradient ((D j I).closed q ∘ block m j) x∈knownSpace W :=
    block_composition_gradient_mem W x ⟨j,by omega⟩ hclosed
      ((D j I).closed_gradient_mem r hparent.width_pos hparent.radius_pos q hq _ _
        hparent.query_mem hparent.columns_mem hparent.blind)
  have hrmem (i : Fin ((D j I).n+1)) :
      gradient (jointRelease m (j+1) (D (j+1) (child I i.val))) x∈knownSpace W :=
    block_composition_gradient_mem W x ⟨j+1,hm⟩ ((D (j+1) (child I i.val)).release_contDiff 3)
      ((D (j+1) (child I i.val)).release_gradient_mem (rc i) (hchild i).radius_pos (hhp i) (hw i)
        _ _ (hchild i).query_mem (hchild i).columns_mem (hchild i).blind)
  have he : jointCarrier m D (d+1) j I 0=(fun y => ((D j I).closed q ∘ block m j) y+
      ∑ i : Fin ((D j I).n+1),jointResidual m j (D j I) i y*
        (jointRelease m (j+1) (D (j+1) (child I i.val)) y-q i)) := by
    funext y
    simp only [jointCarrier,selectedCarrier,padded,Node.closed,Function.comp_apply,
      jointResidual,jointRelease,mul_sub,Finset.sum_sub_distrib]
    ring
  rw [he]
  apply gradient_add_mem (knownSpace W) hcjoint
    (ContDiff.sum (fun i _ => (jointResidual_contDiff m j (D j I) i 3).mul
      ((jointRelease_contDiff m (j+1) (D (j+1) (child I i.val)) 3).sub contDiff_const))) x hcmem
  apply gradient_sum_mem Finset.univ (knownSpace W) _
    (fun i => (jointResidual_contDiff m j (D j I) i 3).mul
      ((jointRelease_contDiff m (j+1) (D (j+1) (child I i.val)) 3).sub contDiff_const))
  intro i _
  apply gradient_mul_mem_of_right_zero (knownSpace W) (jointResidual_contDiff m j (D j I) i 3)
    ((jointRelease_contDiff m (j+1) (D (j+1) (child I i.val)) 3).sub contDiff_const) x
  · simp [jointRelease,block,hm,q]
  · exact gradient_sub_const_mem (knownSpace W)
      (jointRelease_contDiff m (j+1) (D (j+1) (child I i.val)) 3) x (q i) (hrmem i)

end Bilevel.ChiCarrier
