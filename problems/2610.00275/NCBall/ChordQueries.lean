import NCBall.ChordEstimator

/-! # Two actual function values at valid perturbations

For seeds outside the ball's support, degenerate chords use the center.
Consequently both query locations are valid for every seed, not only
almost surely, and their two values equal the defined estimator.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped BigOperators
namespace NCBall

def chordQueryPlus {n : ℕ} (ρ : ℝ) (x : CoordSpace (n + 1))
    (w : CoordSpace (n + 1) × Fin (n + 1)) : CoordSpace (n + 1) :=
  x + if ∑ j, (chordSide w.2 w.1 j) ^ 2 ≤ ρ ^ 2 then
    chordInsert w.2 (chordHalfLength ρ (chordSide w.2 w.1)) (chordSide w.2 w.1) else 0

def chordQueryMinus {n : ℕ} (ρ : ℝ) (x : CoordSpace (n + 1))
    (w : CoordSpace (n + 1) × Fin (n + 1)) : CoordSpace (n + 1) :=
  x + if ∑ j, (chordSide w.2 w.1 j) ^ 2 ≤ ρ ^ 2 then
    chordInsert w.2 (-chordHalfLength ρ (chordSide w.2 w.1)) (chordSide w.2 w.1) else 0

theorem chordQueryPlus_mem {n : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (x : CoordSpace (n + 1))
    (w : CoordSpace (n + 1) × Fin (n + 1)) : chordQueryPlus ρ x w ∈ closedBall x ρ := by
  by_cases hy : ∑ j, (chordSide w.2 w.1 j) ^ 2 ≤ ρ ^ 2
  · simpa only [chordQueryPlus, if_pos hy, mem_closedBall, dist_eq_norm, add_sub_cancel_left,
      sub_zero] using (chordInsert_endpoint_mem w.2 hρ hy).1
  · simpa [chordQueryPlus, hy] using mem_closedBall_self hρ (x := x)

theorem chordQueryMinus_mem {n : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (x : CoordSpace (n + 1))
    (w : CoordSpace (n + 1) × Fin (n + 1)) : chordQueryMinus ρ x w ∈ closedBall x ρ := by
  by_cases hy : ∑ j, (chordSide w.2 w.1 j) ^ 2 ≤ ρ ^ 2
  · simpa only [chordQueryMinus, if_pos hy, mem_closedBall, dist_eq_norm, add_sub_cancel_left,
      sub_zero] using (chordInsert_endpoint_mem w.2 hρ hy).2
  · simpa [chordQueryMinus, hy] using mem_closedBall_self hρ (x := x)

theorem chordEstimate_two_values {n : ℕ} (f : CoordSpace (n + 1) → ℝ) (ρ : ℝ)
    (x : CoordSpace (n + 1)) (w : CoordSpace (n + 1) × Fin (n + 1)) :
    chordEstimate f ρ x w =
      ((n + 1 : ℝ) / (2 * chordHalfLength ρ (chordSide w.2 w.1)) *
        (f (chordQueryPlus ρ x w) - f (chordQueryMinus ρ x w))) • EuclideanSpace.single w.2 1 := by
  by_cases hy : ∑ j, (chordSide w.2 w.1 j) ^ 2 ≤ ρ ^ 2
  · simp only [chordEstimate, chordSlope, chordQueryPlus, chordQueryMinus, if_pos hy]
    congr 1
    ring
  · have hh : chordHalfLength ρ (chordSide w.2 w.1) = 0 :=
      Real.sqrt_eq_zero_of_nonpos (by linarith [not_le.mp hy])
    simp [chordEstimate, chordSlope, chordQueryPlus, chordQueryMinus, hy, hh]

theorem chord_queries_in_padded_ball {n : ℕ} {ρ R : ℝ} (hρ : 0 ≤ ρ)
    (x₀ x : CoordSpace (n + 1)) (hx : ‖x - x₀‖ + ρ ≤ R)
    (w : CoordSpace (n + 1) × Fin (n + 1)) :
    chordQueryPlus ρ x w ∈ closedBall x₀ R ∧ chordQueryMinus ρ x w ∈ closedBall x₀ R := by
  have hdist : dist x x₀ + ρ ≤ R := by simpa only [dist_eq_norm] using hx
  constructor
  · exact (dist_triangle (chordQueryPlus ρ x w) x x₀).trans
      ((add_le_add_right (chordQueryPlus_mem hρ x w) (dist x x₀)).trans
        (by simpa only [add_comm] using hdist))
  · exact (dist_triangle (chordQueryMinus ρ x w) x x₀).trans
      ((add_le_add_right (chordQueryMinus_mem hρ x w) (dist x x₀)).trans
        (by simpa only [add_comm] using hdist))

end NCBall
