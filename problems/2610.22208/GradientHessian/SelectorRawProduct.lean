import GradientHessian.SelectorProductDerivatives
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! The unnormalized first derivative bound needed for a selector port's
third derivative. It remains valid at endpoint probabilities. -/

namespace GradientHessian.SelectorRawProduct
open SelectorBernoulli SelectorProductDerivatives
open Classical
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem erased_mass_sum (p : ι → ℝ) (i : ι) :
    (∑ ω : ι → Bool, ∏ j ∈ (Finset.univ : Finset ι) \ {i}, bitMass (p j) (ω j)) = 2 := by
  have he (ω : ι → Bool) :
      (∏ j ∈ (Finset.univ : Finset ι) \ {i}, bitMass (p j) (ω j)) =
      ∏ j, if j = i then 1 else bitMass (p j) (ω j) := by
    rw [← Fintype.prod_ite_mem]
    apply Finset.prod_congr rfl
    intro j _
    by_cases hj : j = i <;> simp [hj]
  simp_rw [he]
  rw [← Fintype.prod_sum (fun j b => if j = i then (1:ℝ) else bitMass (p j) b)]
  have hs (j : ι) : (∑ b : Bool, if j = i then (1:ℝ) else bitMass (p j) b) =
      if j = i then 2 else 1 := by
    by_cases hj : j = i <;> simp [hj, bitMass]
  simp_rw [hs]
  simp

theorem bitSign_abs (b : Bool) : |bitSign b| = 1 := by cases b <;> norm_num [bitSign]

theorem product_first_raw_formula (p a : ι → ℝ) (ω : ι → Bool) :
    iteratedFDeriv ℝ 1 (ContinuousMultilinearMap.mkPiAlgebra ℝ ι ℝ)
      (fun i => bitMass (p i) (ω i)) (fun _ i => a i*bitSign (ω i)) =
        ∑ i, a i*bitSign (ω i)*(∏ j ∈ (Finset.univ : Finset ι) \ {i}, bitMass (p j) (ω j)) := by
  rw [iteratedFDeriv_one_apply,
    ((ContinuousMultilinearMap.mkPiAlgebra ℝ ι ℝ).hasFDerivAt
      (fun i => bitMass (p i) (ω i))).fderiv]
  simp only [ContinuousMultilinearMap.linearDeriv_apply, ContinuousMultilinearMap.mkPiAlgebra_apply,
    Finset.prod_update_of_mem (Finset.mem_univ _)]

theorem product_first_raw_bound {p : ι → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1)
    (a : ι → ℝ) :
    (∑ ω : ι → Bool, |iteratedFDeriv ℝ 1 (ContinuousMultilinearMap.mkPiAlgebra ℝ ι ℝ)
      (fun i => bitMass (p i) (ω i)) (fun _ i => a i*bitSign (ω i))|) ≤ 2*∑ i, |a i| := by
  simp_rw [product_first_raw_formula]
  calc
    _ ≤ ∑ ω : ι → Bool, ∑ i, |a i*bitSign (ω i)*
        (∏ j ∈ (Finset.univ : Finset ι) \ {i}, bitMass (p j) (ω j))| :=
      Finset.sum_le_sum (fun ω _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ i, |a i| * (∑ ω : ι → Bool,
        ∏ j ∈ (Finset.univ : Finset ι) \ {i}, bitMass (p j) (ω j)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      rw [abs_mul, abs_mul, bitSign_abs, mul_one,
        abs_of_nonneg (Finset.prod_nonneg (fun j _ => bitMass_nonneg (hp j) (ω j)))]
    _ = _ := by simp only [erased_mass_sum, ← Finset.sum_mul]; ring

end
end GradientHessian.SelectorRawProduct
