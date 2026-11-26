import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! # Deterministic geometry of the hidden rooms (Sections 6 and 9) -/

noncomputable section
open Set Metric
open scoped BigOperators

namespace NCBall

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))

/-- Centers are indexed from 0, unlike the manuscript's indexing from 1.
The hidden increments have zero clock coordinate. -/
def roomCenter {n : ℕ} (ρ : ℝ) (U : ℕ → Space n) (j : ℕ) : Space n :=
  (4 * ρ * j) • EuclideanSpace.single 0 1 +
    (16 * ρ) • ∑ i ∈ Finset.range j, U i

theorem roomCenter_zero {n : ℕ} (ρ : ℝ) (U : ℕ → Space n) :
    roomCenter ρ U 0 = 0 := by simp [roomCenter]

theorem roomCenter_clock {n : ℕ} (ρ : ℝ) (U : ℕ → Space n)
    (hU : ∀ i, U i 0 = 0) (j : ℕ) :
    roomCenter ρ U j 0 = 4 * ρ * j := by
  have hs : (∑ i ∈ Finset.range j, U i) 0 = 0 := by
    induction j with
    | zero => simp
    | succ j hj => simp [Finset.sum_range_succ, hj, hU]
  simp [roomCenter, hs, EuclideanSpace.single_apply]

theorem roomCenter_succ {n : ℕ} (ρ : ℝ) (U : ℕ → Space n) (j : ℕ) :
    roomCenter ρ U (j + 1) = roomCenter ρ U j +
      (4 * ρ) • EuclideanSpace.single 0 1 + (16 * ρ) • U j := by
  simp only [roomCenter, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
  module

theorem clock_dist_le {n : ℕ} (x y : Space n) :
    |x 0 - y 0| ≤ dist x y := by
  simpa [dist_eq_norm, Real.norm_eq_abs] using (PiLp.norm_apply_le (x - y) 0)

theorem roomCenter_separated {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (U : ℕ → Space n) (hU : ∀ i, U i 0 = 0) {i j : ℕ} (hij : i < j) :
    4 * ρ ≤ dist (roomCenter ρ U i) (roomCenter ρ U j) := by
  have hc := clock_dist_le (roomCenter ρ U j) (roomCenter ρ U i)
  rw [roomCenter_clock ρ U hU j, roomCenter_clock ρ U hU i] at hc
  have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
  have hnonneg : 0 ≤ 4 * ρ * (j : ℝ) - 4 * ρ * (i : ℝ) := by nlinarith
  rw [abs_of_nonneg hnonneg, dist_comm] at hc
  nlinarith

/-- Equation (6.10): even the closed rooms are disjoint. -/
theorem rooms_disjoint {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (U : ℕ → Space n) (hU : ∀ i, U i 0 = 0) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (closedBall (roomCenter ρ U i) ρ) (closedBall (roomCenter ρ U j) ρ) := by
  have hsep : 4 * ρ ≤ dist (roomCenter ρ U i) (roomCenter ρ U j) := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact roomCenter_separated hρ U hU h
    · simpa [dist_comm] using roomCenter_separated hρ U hU h
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx' := mem_closedBall.mp hx
  have hy' := mem_closedBall.mp hy
  have ht := dist_triangle (roomCenter ρ U i) x (roomCenter ρ U j)
  rw [dist_comm (roomCenter ρ U i) x] at ht
  linarith

theorem room_index_unique {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (U : ℕ → Space n) (hU : ∀ i, U i 0 = 0) {i j : ℕ} {x : Space n}
    (hi : x ∈ closedBall (roomCenter ρ U i) ρ)
    (hj : x ∈ closedBall (roomCenter ρ U j) ρ) : i = j := by
  by_contra h
  exact Set.disjoint_left.mp (rooms_disjoint hρ U hU h) hi hj

/-- Explicit radius estimate on the manuscript's good event. -/
theorem roomCenter_norm_le {n : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (U : ℕ → Space n) (j : ℕ) (hU : ∀ i < j, ‖U i‖ ≤ 2) :
    ‖roomCenter ρ U j‖ ≤ 36 * j * ρ := by
  have hsum : ‖∑ i ∈ Finset.range j, U i‖ ≤ (j : ℝ) * 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range j, ‖U i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range j, (2 : ℝ) :=
        Finset.sum_le_sum fun i hi => hU i (Finset.mem_range.mp hi)
      _ = (j : ℝ) * 2 := by simp
  have hclock : ‖(4 * ρ * j) • (EuclideanSpace.single 0 1 : Space n)‖ = 4 * ρ * j := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), EuclideanSpace.norm_single]
    simp
  have htrans : ‖(16 * ρ) • ∑ i ∈ Finset.range j, U i‖ ≤ (16 * ρ) * ((j : ℝ) * 2) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  have ht := norm_add_le ((4 * ρ * j) • (EuclideanSpace.single 0 1 : Space n))
    ((16 * ρ) • ∑ i ∈ Finset.range j, U i)
  rw [hclock] at ht
  unfold roomCenter
  nlinarith

theorem all_rooms_in_query_ball {n M : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hM : 1 ≤ M)
    (U : ℕ → Space n) (hU : ∀ i < M, ‖U i‖ ≤ 2) {j : ℕ} (hj : j ≤ M)
    {x : Space n} (hx : x ∈ closedBall (roomCenter ρ U j) ρ) :
    x ∈ closedBall (0 : Space n) (37 * M * ρ) := by
  have hcenter := roomCenter_norm_le hρ U j (fun i hi => hU i (lt_of_lt_of_le hi hj))
  have hj' : (j : ℝ) ≤ M := by exact_mod_cast hj
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have ht : ‖x‖ ≤ ‖x - roomCenter ρ U j‖ + ‖roomCenter ρ U j‖ := by
    calc
      ‖x‖ = ‖(x - roomCenter ρ U j) + roomCenter ρ U j‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hx' : ‖x - roomCenter ρ U j‖ ≤ ρ := by
    simpa only [mem_closedBall, dist_eq_norm] using hx
  rw [mem_closedBall, dist_zero_right]
  nlinarith [mul_le_mul_of_nonneg_right hj' hρ,
    mul_le_mul_of_nonneg_right hM' hρ]

/-- A point can be compatible with at most one clock interval, even before
the transverse centers have been revealed (the no-factor-M observation). -/
theorem clock_candidate_unique {ρ s : ℝ} (hρ : 0 < ρ) {i j : ℕ}
    (hi : |s - 4 * ρ * i| ≤ ρ) (hj : |s - 4 * ρ * j| ≤ ρ) : i = j := by
  rcases abs_le.mp hi with ⟨hi₁, hi₂⟩
  rcases abs_le.mp hj with ⟨hj₁, hj₂⟩
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · have h' : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
    nlinarith
  · have h' : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
    nlinarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Equation (9.2), stated directly for the transverse coordinates. -/
theorem next_room_hit_predicts {ρ : ℝ} (hρ : 0 < ρ) (x c u : E)
    (h : ‖x - (c + (16 * ρ) • u)‖ ≤ ρ) :
    ‖(16 * ρ)⁻¹ • (x - c) - u‖ ≤ 1 / 16 := by
  have ha : 16 * ρ ≠ 0 := ne_of_gt (by positivity)
  have heq : (16 * ρ)⁻¹ • (x - c) - u =
      (16 * ρ)⁻¹ • (x - (c + (16 * ρ) • u)) := by
    simp only [sub_add_eq_sub_sub, smul_sub, smul_smul, inv_mul_cancel₀ ha, one_smul]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc
    (16 * ρ)⁻¹ * ‖x - (c + (16 * ρ) • u)‖ ≤ (16 * ρ)⁻¹ * ρ :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = 1 / 16 := by field_simp; ring

/-- Later rooms reduce to the same estimate after subtracting future increments. -/
theorem later_room_hit_predicts {ρ : ℝ} (hρ : 0 < ρ) (x c u future : E)
    (h : ‖x - (c + (16 * ρ) • (u + future))‖ ≤ ρ) :
    ‖(16 * ρ)⁻¹ • (x - c) - future - u‖ ≤ 1 / 16 := by
  have heq : (16 * ρ)⁻¹ • (x - c) - future - u =
      (16 * ρ)⁻¹ • (x - c) - (u + future) := by abel
  rw [heq]
  exact next_room_hit_predicts hρ x c (u + future) h

end NCBall
