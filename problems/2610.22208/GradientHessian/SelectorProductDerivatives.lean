import GradientHessian.SelectorChaos
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! The orthogonal-chaos estimate applied to actual Fréchet derivatives of the
multilinear product. Probabilities equal to zero or one are included. -/

namespace GradientHessian.SelectorProductDerivatives
open SelectorBernoulli SelectorChaos SelectorProfileBounds
open Classical
open scoped BigOperators
noncomputable section

def bitSign (b : Bool) : ℝ := if b then 1 else -1

theorem bitMass_mul_score {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) (b : Bool) :
    bitMass p b*bitScore p b = varianceRoot p*bitSign b := by
  by_cases hr : varianceRoot p = 0
  · simp [bitScore, hr]
  have hs : varianceRoot p^2 = p*(1-p) :=
    Real.sq_sqrt (mul_nonneg hp.1 (sub_nonneg.mpr hp.2))
  cases b <;> simp only [bitMass, bitScore, bitSign, Bool.false_eq_true, if_false, if_true]
  · rw [← mul_div_assoc, div_eq_iff hr]
    nlinarith [hs]
  · rw [← mul_div_assoc, div_eq_iff hr]
    nlinarith [hs]

variable {ι : Type*} [Fintype ι]

theorem product_selected {k : ℕ} (e : Fin k ↪ ι) (x : ι → ℝ)
    (v : Fin k → ι → ℝ) :
    (∏ i, if h : i ∈ Set.range e then v (e.toEquivRange.symm ⟨i,h⟩) i else x i) =
      (∏ l, v l (e l))*(∏ i ∈ (tupleSet e)ᶜ, x i) := by
  classical
  rw [← Finset.prod_mul_prod_compl (tupleSet e)]
  congr 1
  · rw [tupleSet, Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro l _
      simp only [Set.mem_range_self, dif_pos, Function.Embedding.toEquivRange_symm_apply_self]
    · exact fun _ _ _ _ h => e.injective h
  · apply Finset.prod_congr rfl
    intro i hi
    have hn : i ∉ Set.range e := by simpa only [tupleSet, Finset.mem_compl,
      Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using hi
    simp only [dif_neg hn]

theorem product_component {k : ℕ} (e : Fin k ↪ ι) (x : ι → ℝ)
    (v : Fin k → ι → ℝ) :
    (ContinuousMultilinearMap.mkPiAlgebra ℝ ι ℝ).iteratedFDerivComponent e.toEquivRange
      (fun i => x i) v = (∏ l, v l (e l))*(∏ i ∈ (tupleSet e)ᶜ, x i) := by
  classical
  simp only [ContinuousMultilinearMap.iteratedFDerivComponent_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]
  exact product_selected e x v

theorem normalized_product_component {p : ι → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1)
    {k : ℕ} (e : Fin k ↪ ι) (a : Fin k → ι → ℝ) (ω : ι → Bool) :
    (ContinuousMultilinearMap.mkPiAlgebra ℝ ι ℝ).iteratedFDerivComponent e.toEquivRange
      (fun i => bitMass (p i) (ω i))
      (fun l i => varianceRoot (p i)*a l i*bitSign (ω i)) =
        mass p ω*(∏ l, a l (e l))*scoreMonomial p (tupleSet e) ω := by
  classical
  have hs : scoreMonomial p (tupleSet e) ω = ∏ l, bitScore (p (e l)) (ω (e l)) := by
    unfold scoreMonomial tupleSet
    rw [Finset.prod_image]
    exact fun _ _ _ _ h => e.injective h
  have hm : mass p ω = (∏ l, bitMass (p (e l)) (ω (e l)))*
      (∏ i ∈ (tupleSet e)ᶜ, bitMass (p i) (ω i)) := by
    unfold mass
    rw [← Finset.prod_mul_prod_compl (tupleSet e)]
    congr 1
    rw [tupleSet, Finset.prod_image]
    exact fun _ _ _ _ h => e.injective h
  rw [product_component e (fun i => bitMass (p i) (ω i))
    (fun l i => varianceRoot (p i)*a l i*bitSign (ω i)), hs, hm]
  have he : (∏ l, varianceRoot (p (e l))*a l (e l)*bitSign (ω (e l))) =
      ∏ l, a l (e l)*(bitMass (p (e l)) (ω (e l))*bitScore (p (e l)) (ω (e l))) := by
    apply Finset.prod_congr rfl
    intro l _
    rw [bitMass_mul_score (hp (e l))]
    ring
  rw [he]
  simp only [Finset.prod_mul_distrib]
  ring

theorem product_iteratedFDeriv_normalized {p : ι → ℝ}
    (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1) (k : ℕ) (a : Fin k → ι → ℝ) (ω : ι → Bool) :
    iteratedFDeriv ℝ k (ContinuousMultilinearMap.mkPiAlgebra ℝ ι ℝ)
      (fun i => bitMass (p i) (ω i))
      (fun l i => varianceRoot (p i)*a l i*bitSign (ω i)) =
        mass p ω*(∑ e : Fin k ↪ ι, (∏ l, a l (e l))*scoreMonomial p (tupleSet e) ω) := by
  classical
  rw [ContinuousMultilinearMap.iteratedFDeriv_eq]
  simp only [ContinuousMultilinearMap.iteratedFDeriv, ContinuousMultilinearMap.sum_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  simpa only [mul_assoc] using normalized_product_component hp e a ω

/-- An actual tensor estimate for the independent Bernoulli product, with a
constant depending only on the derivative order. -/
theorem product_iteratedFDeriv_normalized_bound {p : ι → ℝ}
    (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1) (k : ℕ) (a : Fin k → ι → ℝ) :
    (∑ ω : ι → Bool, |iteratedFDeriv ℝ k (ContinuousMultilinearMap.mkPiAlgebra ℝ ι ℝ)
      (fun i => bitMass (p i) (ω i))
      (fun l i => varianceRoot (p i)*a l i*bitSign (ω i))|) ≤
        Real.sqrt ((k:ℝ)^k*(∏ l, ∑ i, (a l i)^2)) := by
  simp_rw [product_iteratedFDeriv_normalized hp, abs_mul,
    abs_of_nonneg (mass_nonneg hp _)]
  exact embedding_chaos_bound hp a

end
end GradientHessian.SelectorProductDerivatives
