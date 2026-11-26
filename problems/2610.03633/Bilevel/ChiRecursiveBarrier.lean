import Bilevel.ChiRecursiveObjective
import Bilevel.ChiRecursiveDescent

/-! Finite-depth barrier for the actual recursive objective. The proof
transports derivatives of that objective, rather than assuming a path-wise
global gradient statement. Local certificates are independently verified. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiRecursive
open ChiBoundedChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem Node.residual_abs_bound (D : Node E) (hell : 0≤D.ell) (i : Fin (D.n+1)) (u : E) :
    |D.residual i u|≤gaussianBound*(D.ell*D.width^2) := by
  exact (Finset.single_le_sum (fun k _ => abs_nonneg (D.residual k u)) (Finset.mem_univ i)).trans
    (D.sum_abs_residual_bound hell u)

/-- If every block has its proved local weighted certificate and the actual
recursive payload obeys its proved uniform value budget, an incomplete
release produces a large derivative of one actual objective block. -/
theorem objective_block_barrier
    (D : Geometry E) (ρ R b cap : ℕ → ℝ) (u : ℕ → E)
    {Cs Cr δ : ℝ} (hCs : 0≤Cs) (hCr : 0≤Cr) (hδ : 0≤δ)
    (hδsmall : δ≤releaseTolerance (Cr+Cs))
    (hb : ∀ j,0≤b j) (hbnext : ∀ j,b (j+1)=b j*descentThreshold (Cr+Cs))
    (hell : ∀ j I,0≤(D j I).ell) (hh : ∀ j I,0<(D j I).width)
    (hRpos : ∀ j,0<R j) (hR : ∀ j I,R j=(D j I).radius)
    (hcap : ∀ j I,gaussianBound*((D j I).ell*(D j I).width^2)≤cap (j+1))
    (hs : ∀ j I i,‖fderiv ℝ ((D j I).selector i) (u j)‖≤
      (Cs/(D j I).width)*Real.sqrt ((D j I).selector i (u j)))
    (hr : ∀ j I i,‖fderiv ℝ ((D j I).residual i) (u j)‖≤
      Cr*((D j I).ell*(D j I).width)*Real.sqrt ((D j I).selector i (u j)))
    (hW : ∀ d j I (i : Fin ((D j I).n+1)),
      |payloadValue D d (j+1) (child I i.val) u|≤δ*((D j I).ell*(D j I).width^2))
    (hlocal : ∀ j I w Rp,b j≤w → w≤1 → Rp≤0 → |Rp|≤cap j →
      (D j I).release (u j)<1 →
      (b j*((D j I).ell*(D j I).width)/2≤‖fderiv ℝ ((D j I).localBase (ρ j) w Rp) (u j)‖) ∧
      (|(D j I).coordinates (u j) (Fin.last (D j I).n)|<(D j I).width/2 →
        w*((D j I).ell*(D j I).width)/2≤‖fderiv ℝ ((D j I).localBase (ρ j) w Rp) (u j)‖))
    (d j : ℕ) (I : List ℕ) {w Rp target : ℝ}
    (hw : b j≤w) (hw1 : w≤1) (hRp : Rp≤0) (hRpbound : |Rp|≤cap j)
    (hrelease : (D j I).release (u j)<1)
    (htarget : ∀ k P,j≤k → k≤j+d → target≤b k*((D k P).ell*(D k P).width)/4) :
    ∃ k : ℕ,j≤k ∧ k≤j+d ∧
      target≤‖fderiv ℝ (fun v => objective D ρ R d j I w Rp (Function.update u k v)) (u k)‖ := by
  induction d generalizing j I w Rp with
  | zero =>
    refine ⟨j,le_rfl,by omega,?_⟩
    rw [objective_own_block_derivative D ρ R 0 j I w Rp u (hR j I),
      sliceObjective_leaf_fderiv D j I u (by rw [← hR j I];exact hRpos j)]
    have hl := (hlocal j I w Rp hw hw1 hRp hRpbound hrelease).1
    have hg : 0≤b j*((D j I).ell*(D j I).width) := by
      exact mul_nonneg (hb j) (mul_nonneg (hell j I) (hh j I).le)
    have ht := htarget j I le_rfl (by omega)
    nlinarith only [hl,hg,ht]
  | succ d ih =>
    have hl := hlocal j I w Rp hw hw1 hRp hRpbound hrelease
    have hstop := slice_stop_or_descend D d j I u hCs hCr hδ hδsmall (hell j I) (hh j I)
      (by rw [← hR j I];exact hRpos j) (hb j) hw hw1 (hs j I) (hr j I) (hW d j I) hl.1 hl.2
    rcases hstop with hstop|⟨i,hi,hQ,hwi,hwi1⟩
    · refine ⟨j,le_rfl,by omega,?_⟩
      rw [objective_own_block_derivative D ρ R (d+1) j I w Rp u (hR j I)]
      exact (htarget j I le_rfl (by omega)).trans hstop
    · have hw0 : 0≤w := (hb j).trans hw
      have hir : (D j I).residual i (u j)≤0 := (D j I).residual_nonpos (hell j I) i (u j)
      have hRpchild : w*(D j I).residual i (u j)≤0 := mul_nonpos_of_nonneg_of_nonpos hw0 hir
      have hcapchild : |w*(D j I).residual i (u j)|≤cap (j+1) := by
        rw [abs_mul,abs_of_nonneg hw0]
        have hwabs := mul_le_mul_of_nonneg_right hw1 (abs_nonneg ((D j I).residual i (u j)))
        have hwabs' : w*|(D j I).residual i (u j)|≤|(D j I).residual i (u j)| := by
          simpa only [one_mul] using hwabs
        exact hwabs'.trans
          (((D j I).residual_abs_bound (hell j I) i (u j)).trans (hcap j I))
      have hwi' : b (j+1)≤w*(D j I).selector i (u j) := by rw [hbnext];exact hwi
      obtain ⟨k,hkj,hkend,hbound⟩ := ih (j+1) (child I i.val) hwi' hwi1 hRpchild hcapchild hQ
        (fun k P hk hk' => htarget k P (by omega) (by omega))
      refine ⟨k,by omega,by omega,?_⟩
      have hactive : (D j I).selector i (u j)≠0 := by
        have hth := (descentThreshold_range (add_nonneg hCr hCs)).1
        linarith only [hi,hth]
      rw [objective_descendant_derivative D ρ R d j k I w Rp u (by omega) i hactive]
      exact hbound

end Bilevel.ChiRecursive
