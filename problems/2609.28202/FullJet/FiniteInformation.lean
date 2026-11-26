import FullJet.RowInformation

open scoped BigOperators

namespace FullJet

/-- Finite relative entropy. Theorems state normalization and support
conditions explicitly; zero first weights contribute zero. -/
noncomputable def finiteKL {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ a, p a * Real.log (p a / q a)

theorem mul_log_product_ratio (p q r s : ℝ)
    (hpq : p ≠ 0 → q ≠ 0) (hrs : r ≠ 0 → s ≠ 0) :
    (p * r) * Real.log ((p * r) / (q * s)) =
      (p * r) * Real.log (p / q) + (p * r) * Real.log (r / s) := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hr : r = 0
  · simp [hr]
  rw [show (p * r) / (q * s) = (p / q) * (r / s) by ring,
    Real.log_mul (div_ne_zero hp (hpq hp)) (div_ne_zero hr (hrs hr))]
  ring

/-- Exact chain rule for two finite stages. Zero-probability histories and
zero-probability replies are allowed; absolute continuity is required only
where the first joint law has positive weight. -/
theorem finiteKL_chain_rule {α β : Type*} [Fintype α] [Fintype β]
    (p q : α → ℝ) (r s : α → β → ℝ)
    (hr : ∀ a, ∑ b, r a b = 1)
    (hpq : ∀ a, p a ≠ 0 → q a ≠ 0)
    (hrs : ∀ a, p a ≠ 0 → ∀ b, r a b ≠ 0 → s a b ≠ 0) :
    finiteKL (fun z : α × β => p z.1 * r z.1 z.2) (fun z => q z.1 * s z.1 z.2) =
      finiteKL p q + ∑ a, p a * finiteKL (r a) (s a) := by
  have hrow (a : α) :
      (∑ b, (p a * r a b) * Real.log ((p a * r a b) / (q a * s a b))) =
        p a * Real.log (p a / q a) + p a * finiteKL (r a) (s a) := by
    by_cases hp : p a = 0
    · simp [hp]
    have hpoint (b : β) := mul_log_product_ratio (p a) (q a) (r a b) (s a b) (hpq a) (hrs a hp b)
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib]
    have hfirst : (∑ b, (p a * r a b) * Real.log (p a / q a)) = p a * Real.log (p a / q a) := by
      simp_rw [show ∀ b, (p a * r a b) * Real.log (p a / q a) =
        (p a * Real.log (p a / q a)) * r a b from fun b => by ring]
      rw [← Finset.mul_sum, hr a, mul_one]
    rw [hfirst]
    congr 1
    unfold finiteKL
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  unfold finiteKL
  rw [Fintype.sum_prod_type]
  simp_rw [hrow]
  rw [Finset.sum_add_distrib]
  rfl

/-- A uniform bound on the conditional information increment yields an
additive bound on the joint information. -/
theorem finiteKL_chain_le {α β : Type*} [Fintype α] [Fintype β]
    (p q : α → ℝ) (r s : α → β → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (hr : ∀ a, ∑ b, r a b = 1)
    (hpq : ∀ a, p a ≠ 0 → q a ≠ 0)
    (hrs : ∀ a, p a ≠ 0 → ∀ b, r a b ≠ 0 → s a b ≠ 0)
    (c : ℝ) (hstep : ∀ a, p a ≠ 0 → finiteKL (r a) (s a) ≤ c) :
    finiteKL (fun z : α × β => p z.1 * r z.1 z.2) (fun z => q z.1 * s z.1 z.2) ≤
      finiteKL p q + c := by
  rw [finiteKL_chain_rule p q r s hr hpq hrs]
  apply add_le_add_left
  calc
    ∑ a, p a * finiteKL (r a) (s a) ≤ ∑ a, p a * c := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases hpa : p a = 0
      · simp [hpa]
      · exact mul_le_mul_of_nonneg_left (hstep a hpa) (hp a)
    _ = c := by rw [← Finset.sum_mul, hsum, one_mul]

theorem finiteKL_nonneg {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hsump : ∑ a, p a = 1) (hsumq : ∑ a, q a = 1)
    (hpq : ∀ a, p a ≠ 0 → q a ≠ 0) : 0 ≤ finiteKL p q := by
  have hterm (a : α) : p a - q a ≤ p a * Real.log (p a / q a) := by
    by_cases hpa : p a = 0
    · simp [hpa, hq a]
    have hpp : 0 < p a := lt_of_le_of_ne (hp a) (Ne.symm hpa)
    have hqp : 0 < q a := lt_of_le_of_ne (hq a) (Ne.symm (hpq a hpa))
    have hlog := Real.log_le_sub_one_of_pos (div_pos hqp hpp)
    have hmul := mul_le_mul_of_nonneg_left hlog (hp a)
    rw [Real.log_div hqp.ne' hpp.ne'] at hmul
    rw [Real.log_div hpp.ne' hqp.ne']
    have hcancel : p a * (q a / p a - 1) = q a - p a := by field_simp
    rw [hcancel] at hmul
    linarith
  have h := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hterm a)
  simpa only [Finset.sum_sub_distrib, hsump, hsumq, sub_self, finiteKL] using h

/-- Product distributions have additive relative entropy. -/
theorem finiteKL_product {α β : Type*} [Fintype α] [Fintype β]
    (p q : α → ℝ) (r s : β → ℝ) (hp : ∑ a, p a = 1) (hr : ∑ b, r b = 1)
    (hpq : ∀ a, p a ≠ 0 → q a ≠ 0) (hrs : ∀ b, r b ≠ 0 → s b ≠ 0) :
    finiteKL (fun z : α × β => p z.1 * r z.2) (fun z => q z.1 * s z.2) =
      finiteKL p q + finiteKL r s := by
  rw [finiteKL_chain_rule p q (fun _ => r) (fun _ => s) (fun _ => hr) hpq (fun _ _ => hrs)]
  rw [← Finset.sum_mul, hp, one_mul]

end FullJet
