import Bilevel.ChiCarrierSupportSpace

/-! Support algebra for actual scalar functions on the finite Hilbert
product. The constructed selector gradients are discharged from explicit
blind coordinates, while child support remains a visible induction interface. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive

section Algebra
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem gradient_const_mem (W : Submodule ℝ F) (c : ℝ) (x : F) :
    gradient (fun _ : F => c) x∈W := by
  rw [(hasGradientAt_const x c).gradient]
  exact W.zero_mem

theorem gradient_add_mem (W : Submodule ℝ F) {f g : F → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (x : F) (hfm : gradient f x∈W) (hgm : gradient g x∈W) : gradient (fun y => f y+g y) x∈W := by
  have hd := ((hf.differentiable (by norm_num) x).hasGradientAt.hasFDerivAt).add
    ((hg.differentiable (by norm_num) x).hasGradientAt.hasFDerivAt)
  have hh : HasGradientAt (fun y => f y+g y) (gradient f x+gradient g x) x := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    simpa only [map_add] using hd
  rw [hh.gradient]
  exact W.add_mem hfm hgm

theorem gradient_mul_mem (W : Submodule ℝ F) {f g : F → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (x : F) (hfm : gradient f x∈W) (hgm : gradient g x∈W) : gradient (fun y => f y*g y) x∈W := by
  have hd := ((hf.differentiable (by norm_num) x).hasGradientAt.hasFDerivAt).mul
    ((hg.differentiable (by norm_num) x).hasGradientAt.hasFDerivAt)
  have hh : HasGradientAt (fun y => f y*g y) (f x • gradient g x+g x • gradient f x) x := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    simpa only [map_add,map_smul] using hd
  rw [hh.gradient]
  exact W.add_mem (W.smul_mem _ hgm) (W.smul_mem _ hfm)

theorem gradient_sum_mem {ι : Type*} (S : Finset ι) (W : Submodule ℝ F)
    (f : ι → F → ℝ) (hf : ∀ i,ContDiff ℝ 3 (f i)) (x : F)
    (hm : ∀ i,i∈S → gradient (f i) x∈W) : gradient (fun y => ∑ i ∈ S,f i y) x∈W := by
  have hd := HasFDerivAt.sum (u:=S) (fun i _ => ((hf i).differentiable (by norm_num) x).hasGradientAt.hasFDerivAt)
  have hh : HasGradientAt (fun y => ∑ i ∈ S,f i y) (∑ i ∈ S,gradient (f i) x) x := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    simpa only [map_sum] using hd
  rw [hh.gradient]
  exact W.sum_mem hm
end Algebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem block_composition_gradient_mem {m : ℕ} (W : Fin m → Submodule ℝ E) (x : Blocks m E)
    (i : Fin m) {f : E → ℝ} (hf : ContDiff ℝ 3 f) (hm : gradient f (x i)∈W i) :
    gradient (f ∘ block m i.val) x∈knownSpace W := by
  apply (gradient_mem_knownSpace_iff W x ((hf.comp (block (E:=E) m i.val).contDiff).differentiable (by norm_num) x)).mpr
  intro a
  by_cases he : i=a
  · subst a
    rw [show (fun v => (f ∘ block m i.val) (replaceBlock x i v))=f by
      funext v;simp only [Function.comp_apply,block_replaceBlock,if_pos rfl,if_true]]
    exact hm
  · have hv : i.val≠a.val := by intro h;exact he (Fin.ext h)
    rw [show (fun v => (f ∘ block m i.val) (replaceBlock x a v))=(fun _ => f (block m i.val x)) by
      funext v;simp only [Function.comp_apply,block_replaceBlock,if_neg hv]]
    exact gradient_const_mem (W a) _ _

theorem actual_jointSelector_gradient_mem {m : ℕ} (W : Fin m → Submodule ℝ E) (x : Blocks m E)
    (j : Fin m) (D : Node E) (r : ℕ) (hh : 0<D.width) (hR : 0<D.radius)
    (hu : x j∈W j) (hU : ∀ k : Fin (D.n+1),k.val<r → D.frame (basis k)∈W j)
    (hz : ∀ k : Fin (D.n+1),r≤k.val → |D.coordinates (x j) k|≤D.width/4)
    (i : Fin (D.n+1)) : gradient (jointSelector m j.val D i) x∈knownSpace W :=
  block_composition_gradient_mem W x j (D.selector_contDiff i 3)
    (D.selector_gradient_mem r hh hR i (x j) (W j) hu hU hz)

end Bilevel.ChiCarrier
