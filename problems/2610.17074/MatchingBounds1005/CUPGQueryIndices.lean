import MatchingBounds1005.CUPGPhaseReplies

/-! The exact physical call indices of the finite phase. -/
noncomputable section
namespace MatchingBounds1005.CUPG

theorem rawBodyQuery_zero {d : ℕ} (q α τ L ε : ℝ) (N : ℕ) (p : PhaseData d) :
    rawBodyQuery q α τ L ε N 0 p = p.1 := by simp [rawBodyQuery]
theorem rawBodyQuery_one {d : ℕ} (q α τ L ε : ℝ) (N : ℕ) (p : PhaseData d) :
    rawBodyQuery q α τ L ε N 1 p = rawZ q α p 0 := by simp [rawBodyQuery]

theorem rawBodyQuery_x {d : ℕ} (q α τ L ε : ℝ) (N j : ℕ) (hj : j < N) (p : PhaseData d) :
    rawBodyQuery q α τ L ε N (3 * j + 2) p = rawX q α p j := by
  have hd : (3 * j + 2 - 2) / 3 = j := by omega
  simp (disch := omega) only [rawBodyQuery, hd, if_pos, if_neg]

theorem rawBodyQuery_y_succ {d : ℕ} (q α τ L ε : ℝ) (N j : ℕ) (hj : j < N) (p : PhaseData d) :
    rawBodyQuery q α τ L ε N (3 * (j + 1)) p = rawY q α p (j + 1) := by
  have hd : (3 * (j + 1) - 2) / 3 = j := by omega
  simp (disch := omega) only [rawBodyQuery, hd, if_pos, if_neg]

theorem rawBodyQuery_z_succ {d : ℕ} (q α τ L ε : ℝ) (N j : ℕ) (hj : j < N) (p : PhaseData d) :
    rawBodyQuery q α τ L ε N (3 * (j + 1) + 1) p = rawZ q α p (j + 1) := by
  have hd : (3 * (j + 1) + 1 - 2) / 3 = j := by omega
  simp (disch := omega) only [rawBodyQuery, hd, if_pos, if_neg]

theorem rawBodyQuery_y {d : ℕ} (q α τ L ε : ℝ) (N j : ℕ) (hj : j ≤ N) (p : PhaseData d) :
    rawBodyQuery q α τ L ε N (3 * j) p = rawY q α p j := by
  cases j with
  | zero => rfl
  | succ j => exact rawBodyQuery_y_succ q α τ L ε N j (by omega) p

theorem rawBodyQuery_near {d : ℕ} (q α τ L ε : ℝ) (N j : ℕ) (hj : j < N) (p : PhaseData d) :
    rawBodyQuery q α τ L ε N (3 * N + 2 + 2 * j) p =
      guardNear (rawY q α p (j + 1)) (rawY q α p j) := by
  have hd : (3 * N + 2 + 2 * j - (3 * N + 2)) / 2 = j := by omega
  simp (disch := omega) only [rawBodyQuery, hd, if_pos, if_neg]

theorem rawBodyQuery_far {d : ℕ} (q α τ L ε : ℝ) (N j : ℕ) (hj : j < N) (p : PhaseData d) :
    rawBodyQuery q α τ L ε N (3 * N + 3 + 2 * j) p =
      guardFar (rawY q α p (j + 1)) (rawY q α p j) := by
  have hd : (3 * N + 3 + 2 * j - (3 * N + 2)) / 2 = j := by omega
  simp (disch := omega) only [rawBodyQuery, hd, if_pos, if_neg]

theorem rawBodyQuery_minusY {d : ℕ} (q α τ L ε : ℝ) (N j : ℕ) (hj : j < N) (p : PhaseData d) :
    rawBodyQuery q α τ L ε N (5 * N + 2 + 4 * j) p =
      escapeMinus (rawY q α p j) (rawX q α p j) (16 * τ) := by
  have hd : (5 * N + 2 + 4 * j - (5 * N + 2)) / 4 = j := by omega
  simp (disch := omega) only [rawBodyQuery, hd, if_pos, if_neg]

theorem rawBodyQuery_plusY {d : ℕ} (q α τ L ε : ℝ) (N j : ℕ) (hj : j < N) (p : PhaseData d) :
    rawBodyQuery q α τ L ε N (5 * N + 3 + 4 * j) p =
      escapePlus (rawY q α p j) (rawX q α p j) (16 * τ) := by
  have hd : (5 * N + 3 + 4 * j - (5 * N + 2)) / 4 = j := by omega
  simp (disch := omega) only [rawBodyQuery, hd, if_pos, if_neg]

theorem rawBodyQuery_minusW {d : ℕ} (q α τ L ε : ℝ) (N j : ℕ) (hj : j < N) (p : PhaseData d) :
    rawBodyQuery q α τ L ε N (5 * N + 4 + 4 * j) p =
      escapeMinus (rawWitness q α p (rawStop q α L ε N p)) (rawX q α p j) (16 * τ) := by
  have hd : (5 * N + 4 + 4 * j - (5 * N + 2)) / 4 = j := by omega
  simp (disch := omega) only [rawBodyQuery, hd, if_pos, if_neg]

theorem rawBodyQuery_plusW {d : ℕ} (q α τ L ε : ℝ) (N j : ℕ) (hj : j < N) (p : PhaseData d) :
    rawBodyQuery q α τ L ε N (5 * N + 5 + 4 * j) p =
      escapePlus (rawWitness q α p (rawStop q α L ε N p)) (rawX q α p j) (16 * τ) := by
  have hd : (5 * N + 5 + 4 * j - (5 * N + 2)) / 4 = j := by omega
  simp (disch := omega) only [rawBodyQuery, hd, if_pos, if_neg]

end MatchingBounds1005.CUPG
