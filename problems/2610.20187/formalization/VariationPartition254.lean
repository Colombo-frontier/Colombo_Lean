import IntervalRestart254

noncomputable section
open scoped BigOperators
namespace Paper254

theorem intervalCharge_nonneg (r : ℕ → ℝ) (hr : ∀ t, 0 ≤ r t) (a n : ℕ) :
    0 ≤ intervalCharge r a n := Finset.sum_nonneg (fun k _ => hr (a+k))

/-- Greedy cutting at the first excessive boundary jump, including jumps
larger than V. Internal path length has exactly n-1 jumps. -/
theorem variation_partition_regret (r delta : ℕ → ℝ) (T : ℕ) (C V : ℝ)
    (hdelta : ∀ t, 0 ≤ delta t) (hC : 0 ≤ C) (hV : 0 < V)
    (hlocal : ∀ a n, 0 < n → a+n ≤ T → intervalCharge delta a (n-1) ≤ V →
      intervalCharge r a n ≤ C)
    (a n : ℕ) (hn : a+n ≤ T) :
    intervalCharge r a n ≤ C*(1+intervalCharge delta a (n-1)/V) := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    have hpnonneg := intervalCharge_nonneg delta hdelta a (n-1)
    by_cases hz : n = 0
    · subst n
      simp only [intervalCharge, Finset.range_zero, Finset.sum_empty, Nat.zero_sub,
        zero_div, add_zero, mul_one]
      exact hC
    have hnpos : 0 < n := by omega
    by_cases hsmall : intervalCharge delta a (n-1) ≤ V
    · have hh := hlocal a n hnpos hn hsmall
      have hb : C ≤ C*(1+intervalCharge delta a (n-1)/V) := by
        nlinarith [div_nonneg hpnonneg hV.le]
      exact le_trans hh hb
    have hex : ∃ m, 0 < m ∧ m < n ∧ V < intervalCharge delta a m := by
      have hn2 : 2 ≤ n := by
        by_contra hh
        have he : n = 1 := by omega
        subst n
        simp [intervalCharge, hV.le] at hsmall
      exact ⟨n-1, by omega, by omega, lt_of_not_ge hsmall⟩
    let m := Nat.find hex
    have hm := Nat.find_spec hex
    change 0 < m ∧ m < n ∧ V < intervalCharge delta a m at hm
    have hprev : intervalCharge delta a (m-1) ≤ V := by
      by_contra hh
      have hm2 : 2 ≤ m := by
        by_contra h
        have he : m-1 = 0 := by omega
        rw [he] at hh
        simp [intervalCharge, hV.le] at hh
      have hp : 0 < m-1 ∧ m-1 < n ∧ V < intervalCharge delta a (m-1) :=
        ⟨by omega, by omega, lt_of_not_ge hh⟩
      have hmin := Nat.find_min' hex hp
      change m ≤ m-1 at hmin
      omega
    have hleft := hlocal a m hm.1 (by omega) hprev
    have hright := ih (n-m) (by omega) (a+m) (by omega)
    have hsplit : n = m+(n-m) := by omega
    have hpath : n-1 = m+(n-m-1) := by omega
    have hpay : C ≤ C*(intervalCharge delta a m/V) := by
      have hh : 1 ≤ intervalCharge delta a m/V := (le_div_iff₀ hV).mpr (by linarith [hm.2.2])
      nlinarith
    rw [hsplit, intervalCharge_add]
    have hpathEq : intervalCharge delta a (n-1) =
        intervalCharge delta a m+intervalCharge delta (a+m) (n-m-1) := by
      rw [hpath, intervalCharge_add]
    have hbound : intervalCharge r a m+intervalCharge r (a+m) (n-m) ≤
        C*(1+intervalCharge delta a (n-1)/V) := by
      rw [hpathEq, add_div]
      nlinarith
    simpa only [← hsplit] using hbound

end Paper254
#print axioms Paper254.variation_partition_regret
