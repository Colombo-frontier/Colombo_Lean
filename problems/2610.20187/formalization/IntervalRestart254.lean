import Energy254
import Mathlib.Data.Nat.Log

noncomputable section
open scoped BigOperators
namespace Paper254

def intervalCharge (r : ℕ → ℝ) (a n : ℕ) : ℝ := ∑ k ∈ Finset.range n, r (a+k)

theorem intervalCharge_add (r : ℕ → ℝ) (a n m : ℕ) :
    intervalCharge r a (n+m) = intervalCharge r a n+intervalCharge r (a+n) m := by
  simp only [intervalCharge, Finset.sum_range_add, Nat.add_assoc]

/-- The negative-prefix restart argument, directly over actual intervals.
The two alternatives represent a surviving good suffix or the first bad
prefix; no recursion tree or total-regret bound is assumed. -/
theorem interval_restart_bound (r : ℕ → ℝ) (T L : ℕ) (C B : ℝ)
    (hC : 0 ≤ C) (hB : 2*C*L ≤ B)
    (hcase : ∀ a n, 0 < n → a+n ≤ T → ∃ k, 2*k < n ∧
      (intervalCharge r (a+k) (n-k) ≤ C ∨
        ∃ j, 0 < j ∧ j ≤ n-k ∧ intervalCharge r (a+k) j ≤ -B))
    (a n l : ℕ) (hn : a+n ≤ T) (hl : l ≤ L) (hsize : n < 2^l) :
    intervalCharge r a n ≤ C*l := by
  induction n using Nat.strong_induction_on generalizing a l with
  | h n ih =>
    by_cases hz : n = 0
    · subst n
      simp only [intervalCharge, Finset.range_zero, Finset.sum_empty]
      positivity
    have hnpos : 0 < n := by omega
    have hlpos : 0 < l := by
      by_contra hh
      have he : l = 0 := by omega
      rw [he] at hsize
      norm_num at hsize
      omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hlpos)
    obtain ⟨k, hk, hgood | hbad⟩ := hcase a n hnpos hn
    · have hklt : k < n := by omega
      have hkpow : k < 2^m := by
        have hh : 2^(m+1) = 2*2^m := by rw [pow_succ]; omega
        rw [hh] at hsize
        omega
      have hleft := ih k hklt a m (by omega) (by omega) hkpow
      have hsplit : n = k+(n-k) := by omega
      rw [hsplit, intervalCharge_add]
      have hc : (m+1 : ℕ) = m+1 := rfl
      push_cast
      nlinarith
    · obtain ⟨j, hjpos, hj, hbad⟩ := hbad
      have hklt : k < n := by omega
      have hrlt : n-k-j < n := by omega
      have hfull : n < 2^L := lt_of_lt_of_le hsize
        (Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hl)
      have hleft := ih k hklt a L (by omega) le_rfl (by omega)
      have hright := ih (n-k-j) hrlt (a+k+j) L (by omega) le_rfl (by omega)
      have hsplit : n = k+(j+(n-k-j)) := by omega
      rw [hsplit, intervalCharge_add, intervalCharge_add]
      have hnC : 0 ≤ C*(m+1 : ℕ) := mul_nonneg hC (Nat.cast_nonneg _)
      nlinarith

end Paper254
#print axioms Paper254.interval_restart_bound
