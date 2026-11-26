import GradientHessian.SelectorRawProduct
import GradientHessian.LocalizedProductDerivatives

/-! Faà di Bruno for the actual finite Bernoulli mass. The formula keeps the
register index visible, permitting bounds without the number of registers. -/

namespace GradientHessian.SelectorChainRule
open SelectorBernoulli SelectorProductDerivatives LocalizedProductDerivatives
open Classical
open scoped BigOperators
noncomputable section

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem product_contDiff : ContDiff ℝ 3 (ContinuousMultilinearMap.mkPiAlgebra ℝ ι ℝ) := by
  exact contDiff_prod (fun i _ => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).contDiff)

def bitVector (q : ι → F → ℝ) (ω : ι → Bool) (x : F) : ι → ℝ :=
  fun i => bitMass (q i x) (ω i)

theorem bit_contDiff (q : F → ℝ) (hq : ContDiff ℝ 3 q) (b : Bool) :
    ContDiff ℝ 3 (fun x => bitMass (q x) b) := by
  cases b
  · exact contDiff_const.sub hq
  · exact hq

theorem bitVector_contDiff (q : ι → F → ℝ) (hq : ∀ i, ContDiff ℝ 3 (q i)) (ω : ι → Bool) :
    ContDiff ℝ 3 (bitVector q ω) := contDiff_pi.mpr (fun i => bit_contDiff (q i) (hq i) (ω i))

theorem bit_derivative (q : F → ℝ) (hq : ContDiff ℝ 3 q) (b : Bool)
    {n : ℕ} (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (x : F) (v : Fin n → F) :
    iteratedFDeriv ℝ n (fun y => bitMass (q y) b) x v =
      bitSign b*iteratedFDeriv ℝ n q x v := by
  cases b
  · have he : (fun y => bitMass (q y) false) = fun y => -q y + 1 := by funext y; simp [bitMass]; ring
    rw [he, iteratedFDeriv_add_const_of_pos hn1
      (hq.neg.of_le (by exact_mod_cast hn3)).contDiffAt]
    simp only [← Pi.neg_apply, iteratedFDeriv_neg_apply, ContinuousMultilinearMap.neg_apply]
    norm_num [bitSign]
  · simp only [bitMass, if_true, bitSign, one_mul]

theorem bitVector_derivative (q : ι → F → ℝ) (hq : ∀ i, ContDiff ℝ 3 (q i))
    (ω : ι → Bool) {n : ℕ} (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (x : F) (v : Fin n → F) (i : ι) :
    (iteratedFDeriv ℝ n (bitVector q ω) x v) i =
      bitSign (ω i)*iteratedFDeriv ℝ n (q i) x v := by
  have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).iteratedFDeriv_comp_left
    (x := x) (bitVector_contDiff q hq ω).contDiffAt (by exact_mod_cast hn3 : (n : WithTop ℕ∞) ≤ 3)
  have he := congrArg (fun T => T v) h
  change iteratedFDeriv ℝ n (fun y => bitMass (q i y) (ω i)) x v =
    (iteratedFDeriv ℝ n (bitVector q ω) x v) i at he
  rw [← he]
  exact bit_derivative (q i) (hq i) (ω i) hn1 hn3 x v

theorem mass_contDiff (q : ι → F → ℝ) (hq : ∀ i, ContDiff ℝ 3 (q i)) (ω : ι → Bool) :
    ContDiff ℝ 3 (fun x => mass (fun i => q i x) ω) := by
  exact product_contDiff.comp (bitVector_contDiff q hq ω)

theorem mass_iteratedFDeriv (q : ι → F → ℝ) (hq : ∀ i, ContDiff ℝ 3 (q i)) (ω : ι → Bool)
    {n : ℕ} (hn : n ≤ 3) (x : F) (v : Fin n → F) :
    iteratedFDeriv ℝ n (fun y => mass (fun i => q i y) ω) x v =
      ∑ c : OrderedFinpartition n,
        iteratedFDeriv ℝ c.length (ContinuousMultilinearMap.mkPiAlgebra ℝ ι ℝ)
          (bitVector q ω x) (fun l i => bitSign (ω i)*
            iteratedFDeriv ℝ (c.partSize l) (q i) x (v ∘ c.emb l)) := by
  change iteratedFDeriv ℝ n ((ContinuousMultilinearMap.mkPiAlgebra ℝ ι ℝ) ∘ bitVector q ω) x v = _
  rw [iteratedFDeriv_comp product_contDiff.contDiffAt
    (bitVector_contDiff q hq ω).contDiffAt (by exact_mod_cast hn)]
  simp only [FormalMultilinearSeries.taylorComp, ContinuousMultilinearMap.sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply, ftaylorSeries]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  funext l i
  exact bitVector_derivative q hq ω (c.partSize_pos l) ((c.partSize_le l).trans hn) x (v ∘ c.emb l) i

end
end GradientHessian.SelectorChainRule
