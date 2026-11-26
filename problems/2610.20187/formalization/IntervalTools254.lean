import VariationPartition254

noncomputable section
open scoped BigOperators
namespace Paper254

theorem intervalCharge_add_functions (r s : ℕ → ℝ) (a n : ℕ) :
    intervalCharge (fun t => r t+s t) a n = intervalCharge r a n+intervalCharge s a n := by
  simp only [intervalCharge, Finset.sum_add_distrib]

theorem intervalCharge_shift (r : ℕ → ℝ) (s a n : ℕ) :
    intervalCharge (fun t => r (s+t)) a n = intervalCharge r (s+a) n := by
  simp only [intervalCharge, Nat.add_assoc]

theorem intervalCharge_subinterval_le (r : ℕ → ℝ) (hr : ∀ t, 0 ≤ r t)
    (a n b m : ℕ) (hab : a ≤ b) (hend : b+m ≤ a+n) :
    intervalCharge r b m ≤ intervalCharge r a n := by
  have he : n = (b-a)+(m+(a+n-b-m)) := by omega
  have ha : a+(b-a) = b := by omega
  conv_rhs => rw [he, intervalCharge_add, intervalCharge_add, ha]
  have hl := intervalCharge_nonneg r hr a (b-a)
  have hright := intervalCharge_nonneg r hr (b+m) (a+n-b-m)
  linarith

end Paper254
#print axioms Paper254.intervalCharge_subinterval_le
