import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-! The analytic, scalar part of Schatten compression. The connection between
compressed matrix eigenvalues and the comparison list is NOT established here. -/

namespace LowRank
open Set
open scoped BigOperators

theorem exists_positive_rpow_slope {a b r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      x ≤ y → c * (y - x) ≤ y ^ r - x ^ r := by
  let g : ℝ → ℝ := fun x => r * x ^ (r - 1)
  have hg : ContinuousOn g (Icc a b) := by
    intro x hx
    exact (continuousAt_const.mul (Real.continuousAt_rpow_const x (r - 1)
      (Or.inl (ne_of_gt (ha.trans_le hx.1))))).continuousWithinAt
  obtain ⟨z, hz, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hg
  refine ⟨g z, mul_pos hr (Real.rpow_pos_of_pos (ha.trans_le hz.1) _), ?_⟩
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | hxy
  · simp
  have hcont : ContinuousOn (fun u : ℝ => u ^ r) (Icc x y) := by
    intro u hu
    exact (Real.hasDerivAt_rpow_const
      (Or.inl (ne_of_gt ((ha.trans_le hx.1).trans_le hu.1)))).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun u : ℝ => u ^ r) (Ioo x y) := by
    intro u hu
    exact (Real.hasDerivAt_rpow_const
      (Or.inl (ne_of_gt ((ha.trans_le hx.1).trans hu.1)))).differentiableAt.differentiableWithinAt
  obtain ⟨u, hu, hder⟩ := exists_deriv_eq_slope (fun u : ℝ => u ^ r) hxy hcont hdiff
  have huab : u ∈ Icc a b := ⟨hx.1.trans hu.1.le, hu.2.le.trans hy.2⟩
  have hder' := (Real.hasDerivAt_rpow_const (p := r)
    (Or.inl (ne_of_gt (ha.trans_le huab.1)))).deriv
  rw [hder'] at hder
  have hmin' : g z ≤ (y ^ r - x ^ r) / (y - x) := by
    rw [← hder]
    exact hmin huab
  exact (le_div_iff₀ (sub_pos.mpr hxy)).mp hmin'

/-- Sum of the scalar inequalities, covering all positive real exponents,
including `r = p/2 < 1`. -/
theorem finite_spectral_compression {ι : Type*} [Fintype ι]
    {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ ∀ (θ lam : ι → ℝ),
      (∀ i, θ i ∈ Icc a b) → (∀ i, lam i ∈ Icc a b) →
      (∀ i, lam i ≤ θ i) →
      c * (∑ i, θ i - ∑ i, lam i) ≤ ∑ i, θ i ^ r - ∑ i, lam i ^ r := by
  obtain ⟨c, hc, hbound⟩ := exists_positive_rpow_slope ha hab hr
  refine ⟨c, hc, ?_⟩
  intro θ lam hθ hlam hsep
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => hbound (lam i) (hlam i) (θ i) (hθ i) (hsep i))
  simpa only [← Finset.mul_sum, Finset.sum_sub_distrib] using h

end LowRank
