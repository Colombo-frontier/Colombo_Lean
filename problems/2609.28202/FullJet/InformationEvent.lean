import FullJet.FiniteInformation

open scoped BigOperators

namespace FullJet

/-- Finite Gibbs variational inequality, including distributions with zeros. -/
theorem finiteKL_variational {α : Type*} [Fintype α]
    (p q f : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hsump : ∑ a, p a = 1) (hsumq : ∑ a, q a = 1)
    (hpq : ∀ a, p a ≠ 0 → q a ≠ 0) :
    ∑ a, p a * f a ≤ finiteKL p q + Real.log (∑ a, q a * Real.exp (f a)) := by
  let Z := ∑ a, q a * Real.exp (f a)
  have hZ : 0 < Z := by
    have hex : ∃ a, 0 < q a := by
      by_contra hn
      push_neg at hn
      have hz : ∀ a, q a = 0 := fun a => le_antisymm (hn a) (hq a)
      simp [hz] at hsumq
    obtain ⟨a, hqa⟩ := hex
    exact lt_of_lt_of_le (mul_pos hqa (Real.exp_pos _))
      (Finset.single_le_sum (fun b _ => mul_nonneg (hq b) (Real.exp_pos _).le) (Finset.mem_univ a))
  let r := fun a => q a * Real.exp (f a) / Z
  have hr : ∀ a, 0 ≤ r a := fun a => div_nonneg (mul_nonneg (hq a) (Real.exp_pos _).le) hZ.le
  have hsumr : ∑ a, r a = 1 := by
    dsimp only [r]
    rw [← Finset.sum_div]
    exact div_self hZ.ne'
  have hpr : ∀ a, p a ≠ 0 → r a ≠ 0 := fun a hpa =>
    div_ne_zero (mul_ne_zero (hpq a hpa) (Real.exp_ne_zero _)) hZ.ne'
  have hpoint (a : α) : p a * Real.log (p a / r a) =
      p a * Real.log (p a / q a) - p a * f a + p a * Real.log Z := by
    by_cases hpa : p a = 0
    · simp [hpa]
    have hqa := hpq a hpa
    dsimp only [r]
    rw [Real.log_div hpa (hpr a hpa), Real.log_div (mul_ne_zero hqa (Real.exp_ne_zero _)) hZ.ne',
      Real.log_mul hqa (Real.exp_ne_zero _), Real.log_exp, Real.log_div hpa hqa]
    ring
  have h := finiteKL_nonneg p r hp hr hsump hsumr hpr
  unfold finiteKL at h
  simp_rw [hpoint] at h
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hsump, one_mul] at h
  change 0 ≤ finiteKL p q - (∑ a, p a * f a) + Real.log Z at h
  linarith

/-- An event rare under the reference law cannot become likely without
spending relative entropy. This is the finite event bound used for alignment. -/
theorem finiteKL_event_bound {α : Type*} [Fintype α] [DecidableEq α]
    (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hsump : ∑ a, p a = 1) (hsumq : ∑ a, q a = 1)
    (hpq : ∀ a, p a ≠ 0 → q a ≠ 0) (A : Finset α)
    (hA : 0 < ∑ a ∈ A, q a) :
    (∑ a ∈ A, p a) * Real.log (1 / ∑ a ∈ A, q a) ≤ finiteKL p q + Real.log 2 := by
  let Q := ∑ a ∈ A, q a
  let t := Real.log (1 / Q)
  let f := fun a => if a ∈ A then t else 0
  have h := finiteKL_variational p q f hp hq hsump hsumq hpq
  have hleft : (∑ a, p a * f a) = (∑ a ∈ A, p a) * t := by
    simp only [f, mul_ite, mul_zero]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_mul]
  have hZ : (∑ a, q a * Real.exp (f a)) = 2 - Q := by
    have hexp : Real.exp t = 1 / Q := Real.exp_log (one_div_pos.mpr hA)
    have hpoint (a : α) : q a * Real.exp (f a) = q a + (if a ∈ A then q a * (1 / Q - 1) else 0) := by
      by_cases ha : a ∈ A <;> simp [f, ha, hexp] <;> ring
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, hsumq, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.univ_inter, ← Finset.sum_mul]
    change 1 + Q * (1 / Q - 1) = 2 - Q
    field_simp
    <;> ring
  rw [hleft, hZ] at h
  have hQ1 : Q ≤ 1 := by
    calc
      Q ≤ ∑ a, q a := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ => hq a)
      _ = 1 := hsumq
  have hlog : Real.log (2 - Q) ≤ Real.log 2 :=
    Real.log_le_log (by linarith) (by linarith)
  exact h.trans (add_le_add_left hlog _)

end FullJet
