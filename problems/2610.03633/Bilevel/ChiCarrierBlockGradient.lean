import Bilevel.ChiCarrierSupportAlgebra

/-! Exact gradients of actual block embeddings and finite scalar sums,
used to derive the public radial coefficient in each inverse equation. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiCarrier
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradient_block_composition {m : ℕ} (x : Blocks m E) (i : Fin m)
    {f : E → ℝ} (hf : ContDiff ℝ 3 f) :
    gradient (f ∘ block m i.val) x=insertion m i (gradient f (x i)) := by
  ext k
  rw [← gradient_replaceBlock x k ((hf.comp (block (E:=E) m i.val).contDiff).differentiable (by norm_num) x)]
  by_cases hki : k=i
  · subst k
    rw [show (fun v => (f ∘ block m i.val) (replaceBlock x i v))=f by
      funext v;simp only [Function.comp_apply,block_replaceBlock,if_pos rfl,if_true]]
    simp only [insertion_apply,if_pos rfl,if_true]
  · have hv : i.val≠k.val := by intro he;exact hki (Fin.ext he.symm)
    rw [show (fun v => (f ∘ block m i.val) (replaceBlock x k v))=(fun _ => f (block m i.val x)) by
      funext v;simp only [Function.comp_apply,block_replaceBlock,if_neg hv]]
    rw [(hasGradientAt_const (x k) (f (block m i.val x))).gradient,insertion_apply,if_neg hki]

theorem gradient_finset_sum {ι : Type*} (S : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i,ContDiff ℝ 3 (f i)) (x : E) :
    gradient (fun y => ∑ i ∈ S,f i y) x=∑ i ∈ S,gradient (f i) x := by
  have hd := HasFDerivAt.sum (u:=S) (fun i _ => ((hf i).differentiable (by norm_num) x).hasGradientAt.hasFDerivAt)
  have hh : HasGradientAt (fun y => ∑ i ∈ S,f i y) (∑ i ∈ S,gradient (f i) x) x := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    simpa only [map_sum] using hd
  exact hh.gradient

end Bilevel.ChiCarrier
