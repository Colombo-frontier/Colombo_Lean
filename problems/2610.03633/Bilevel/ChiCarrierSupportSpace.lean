import Bilevel.ChiCarrierBlockSlice
import Bilevel.ChiRecursiveCarrierLocality

/-! The actual finite Hilbert restricted space and exact block-gradient
identity. These geometric interfaces preserve every block of the concrete
construction and do not replace its support obligations by norm bounds. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiCarrier
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def knownSpace {m : ℕ} (W : Fin m → Submodule ℝ E) : Submodule ℝ (Blocks m E) where
  carrier := {x | ∀ i,x i∈W i}
  zero_mem' := by intro i;exact (W i).zero_mem
  add_mem' := by intro x y hx hy i;exact (W i).add_mem (hx i) (hy i)
  smul_mem' := by intro c x hx i;exact (W i).smul_mem c (hx i)

omit [CompleteSpace E] in
theorem mem_knownSpace {m : ℕ} (W : Fin m → Submodule ℝ E) (x : Blocks m E) :
    x∈knownSpace W ↔ ∀ i,x i∈W i := Iff.rfl

omit [CompleteSpace E] in
theorem inner_insertion_right {m : ℕ} (x : Blocks m E) (i : Fin m) (v : E) :
    ⟪x,insertion m i v⟫=⟪x i,v⟫ := by
  simp only [PiLp.inner_apply,insertion_apply]
  rw [Finset.sum_eq_single i]
  · simp only [if_pos rfl,if_true]
  · intro k _ hki
    rw [if_neg hki,inner_zero_right]
  · simp

theorem gradient_replaceBlock {m : ℕ} {f : Blocks m E → ℝ} (x : Blocks m E) (i : Fin m)
    (hf : DifferentiableAt ℝ f x) :
    gradient (fun v => f (replaceBlock x i v)) (x i)=(gradient f x) i := by
  have hd := hf.hasGradientAt.hasFDerivAt
  have hdc : HasFDerivAt f (InnerProductSpace.toDual ℝ (Blocks m E) (gradient f x))
      (replaceBlock x i (x i)) := by simpa only [replaceBlock_self] using hd
  have hcomp := hdc.comp (x i) (replaceBlock_hasFDerivAt x i (x i))
  have hg : HasGradientAt (fun v => f (replaceBlock x i v)) ((gradient f x) i) (x i) := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    convert hcomp using 1
    ext v
    simp only [InnerProductSpace.toDual_apply,ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap,inner_insertion_right]
  exact hg.gradient

theorem gradient_mem_knownSpace_iff {m : ℕ} {f : Blocks m E → ℝ} (W : Fin m → Submodule ℝ E)
    (x : Blocks m E) (hf : DifferentiableAt ℝ f x) :
    gradient f x∈knownSpace W ↔
      ∀ i,gradient (fun v => f (replaceBlock x i v)) (x i)∈W i := by
  rw [mem_knownSpace]
  apply forall_congr'
  intro i
  rw [gradient_replaceBlock x i hf]

omit [CompleteSpace E] in
theorem block_replaceBlock {m : ℕ} (x : Blocks m E) (i : Fin m) (j : ℕ) (v : E) :
    block m j (replaceBlock x i v)=if j=i.val then v else block m j x := by
  have hh := congrFun (padded_replaceBlock x i v) j
  simpa only [padded,Function.update_apply] using hh

end Bilevel.ChiCarrier
