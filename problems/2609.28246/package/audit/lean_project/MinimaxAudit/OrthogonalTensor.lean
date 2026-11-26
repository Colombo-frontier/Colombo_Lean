import Mathlib

/-!
# Dimension-free finite module-product inequality

This is the numerical core of the manuscript's orthogonal-module tensor bound
(lines 609--617). It holds for arbitrary finite numbers of modules and tensor
arguments. No derivative tensor or family of orthogonal projections is silently
introduced: the projection-square estimate must be supplied when applying it.
-/

namespace MinimaxAudit

/-- Nonnegative module coefficients with square sums at most one in each
argument column have total module-product sum at most one, for any number of
arguments at least two. The index set need not be an initial interval. -/
theorem module_product_sum_le_one {J L : Type*} [DecidableEq L]
    (modules : Finset J) (arguments : Finset L) (a : J → L → ℝ)
    {l0 l1 : L} (hl0 : l0 ∈ arguments) (hl1 : l1 ∈ arguments) (hne : l0 ≠ l1)
    (hnonneg : ∀ j ∈ modules, ∀ l ∈ arguments, 0 ≤ a j l)
    (hsquares : ∀ l ∈ arguments, ∑ j ∈ modules, (a j l) ^ 2 ≤ 1) :
    (∑ j ∈ modules, ∏ l ∈ arguments, a j l) ≤ 1 := by
  have hone : ∀ j ∈ modules, ∀ l ∈ arguments, a j l ≤ 1 := by
    intro j hj l hl
    have hsingle : (a j l) ^ 2 ≤ ∑ i ∈ modules, (a i l) ^ 2 :=
      Finset.single_le_sum (fun i _hi => sq_nonneg (a i l)) hj
    have hsum := hsquares l hl
    have ha := hnonneg j hj l hl
    nlinarith
  have hpair : ({l0, l1} : Finset L) ⊆ arguments := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact hl0
    · exact hl1
  have hpoint : ∀ j ∈ modules,
      (∏ l ∈ arguments, a j l) ≤ a j l0 * a j l1 := by
    intro j hj
    have h := Finset.prod_le_prod_of_subset_of_le_one hpair
      (fun l hl => hnonneg j hj l hl) (fun l hl _ => hone j hj l hl)
    simpa [hne] using h
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq modules
    (fun j => a j l0) (fun j => a j l1)
  have hs0 := hsquares l0 hl0
  have hs1 := hsquares l1 hl1
  have hsqnonneg : 0 ≤ ∑ j ∈ modules, (a j l1) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hprod := mul_le_mul hs0 hs1 hsqnonneg (show (0 : ℝ) ≤ 1 by norm_num)
  have hpairSum : (∑ j ∈ modules, a j l0 * a j l1) ≤ 1 := by
    nlinarith
  exact (Finset.sum_le_sum hpoint).trans hpairSum

/-- The same estimate for nonnegative coefficient bounds multiplied by a
uniform derivative constant. No module-count factor appears. -/
theorem module_product_sum_le_constant {J L : Type*} [DecidableEq L]
    (modules : Finset J) (arguments : Finset L) (a : J → L → ℝ)
    {l0 l1 : L} (hl0 : l0 ∈ arguments) (hl1 : l1 ∈ arguments) (hne : l0 ≠ l1)
    (hnonneg : ∀ j ∈ modules, ∀ l ∈ arguments, 0 ≤ a j l)
    (hsquares : ∀ l ∈ arguments, ∑ j ∈ modules, (a j l) ^ 2 ≤ 1)
    {C : ℝ} (hC : 0 ≤ C) :
    C * (∑ j ∈ modules, ∏ l ∈ arguments, a j l) ≤ C := by
  have h := module_product_sum_le_one modules arguments a hl0 hl1 hne hnonneg hsquares
  simpa using mul_le_mul_of_nonneg_left h hC

/-- Combining actual scalar module evaluations with the numerical projection
estimate gives the desired dimension-free absolute-value bound. Each module's
multilinear evaluation estimate remains an explicit hypothesis. -/
theorem module_evaluation_sum_bound {J L : Type*} [DecidableEq L]
    (modules : Finset J) (arguments : Finset L) (a : J → L → ℝ) (value : J → ℝ)
    {l0 l1 : L} (hl0 : l0 ∈ arguments) (hl1 : l1 ∈ arguments) (hne : l0 ≠ l1)
    (hnonneg : ∀ j ∈ modules, ∀ l ∈ arguments, 0 ≤ a j l)
    (hsquares : ∀ l ∈ arguments, ∑ j ∈ modules, (a j l) ^ 2 ≤ 1)
    {C : ℝ} (hC : 0 ≤ C)
    (hvalue : ∀ j ∈ modules, |value j| ≤ C * ∏ l ∈ arguments, a j l) :
    |∑ j ∈ modules, value j| ≤ C := by
  calc
    |∑ j ∈ modules, value j| ≤ ∑ j ∈ modules, |value j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ modules, C * ∏ l ∈ arguments, a j l :=
      Finset.sum_le_sum hvalue
    _ = C * (∑ j ∈ modules, ∏ l ∈ arguments, a j l) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ C := module_product_sum_le_constant modules arguments a
      hl0 hl1 hne hnonneg hsquares hC

/-- Homogeneous form: column square sums bounded by b(l)^2 give a product
sum bounded by the product of all b(l), including zero columns. -/
theorem module_product_sum_le_product {J L : Type*} [DecidableEq L]
    (modules : Finset J) (arguments : Finset L) (a : J → L → ℝ) (b : L → ℝ)
    {l0 l1 : L} (hl0 : l0 ∈ arguments) (hl1 : l1 ∈ arguments) (hne : l0 ≠ l1)
    (hnonneg : ∀ j ∈ modules, ∀ l ∈ arguments, 0 ≤ a j l)
    (hb : ∀ l ∈ arguments, 0 ≤ b l)
    (hsquares : ∀ l ∈ arguments, ∑ j ∈ modules, (a j l) ^ 2 ≤ (b l) ^ 2) :
    (∑ j ∈ modules, ∏ l ∈ arguments, a j l) ≤ ∏ l ∈ arguments, b l := by
  by_cases hz : ∃ l ∈ arguments, b l = 0
  · obtain ⟨l, hl, hbl⟩ := hz
    have hcol : ∀ j ∈ modules, a j l = 0 := by
      intro j hj
      have hs : (a j l) ^ 2 ≤ ∑ i ∈ modules, (a i l) ^ 2 :=
        Finset.single_le_sum (fun i _ => sq_nonneg (a i l)) hj
      have hbound := hsquares l hl
      rw [hbl] at hbound
      nlinarith [sq_nonneg (a j l)]
    have hsum : (∑ j ∈ modules, ∏ k ∈ arguments, a j k) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact Finset.prod_eq_zero hl (hcol j hj)
    rw [hsum]
    exact Finset.prod_nonneg hb
  · have hbpos : ∀ l ∈ arguments, 0 < b l := by
      intro l hl
      exact lt_of_le_of_ne (hb l hl) (Ne.symm (fun h => hz ⟨l, hl, h⟩))
    have hnormalized : ∀ l ∈ arguments,
        ∑ j ∈ modules, (a j l / b l) ^ 2 ≤ 1 := by
      intro l hl
      calc
        (∑ j ∈ modules, (a j l / b l) ^ 2) =
            (∑ j ∈ modules, (a j l) ^ 2) / (b l) ^ 2 := by
          simp_rw [div_pow]
          exact (Finset.sum_div _ _ _).symm
        _ ≤ 1 := (div_le_one (sq_pos_of_pos (hbpos l hl))).2 (hsquares l hl)
    have h := module_product_sum_le_one modules arguments (fun j l => a j l / b l)
      hl0 hl1 hne
      (fun j hj l hl => div_nonneg (hnonneg j hj l hl) (hb l hl)) hnormalized
    have hsum : (∑ j ∈ modules, ∏ l ∈ arguments, a j l / b l) =
        (∑ j ∈ modules, ∏ l ∈ arguments, a j l) / (∏ l ∈ arguments, b l) := by
      simp_rw [Finset.prod_div_distrib]
      exact (Finset.sum_div _ _ _).symm
    rw [hsum] at h
    exact (div_le_one (Finset.prod_pos hbpos)).1 h

end MinimaxAudit
