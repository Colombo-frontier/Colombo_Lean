import NCBall.LipschitzInterval
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Coordinate chords of a Euclidean ball -/

noncomputable section
open MeasureTheory Set Metric
open scoped BigOperators
namespace NCBall

abbrev CoordSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)

def chordInsert {n : ℕ} (i : Fin (n + 1)) (t : ℝ) (y : Fin n → ℝ) : CoordSpace (n + 1) :=
  (WithLp.equiv 2 _).symm (i.insertNth t y)

theorem chordInsert_apply_self {n : ℕ} (i : Fin (n + 1)) (t : ℝ) (y : Fin n → ℝ) :
    chordInsert i t y i = t := Fin.insertNth_apply_same (α := fun _ => ℝ) i t y

theorem chordInsert_apply_other {n : ℕ} (i : Fin (n + 1)) (t : ℝ) (y : Fin n → ℝ) (j : Fin n) :
    chordInsert i t y (i.succAbove j) = y j := Fin.insertNth_apply_succAbove (α := fun _ => ℝ) i t y j

theorem chordInsert_norm_sq {n : ℕ} (i : Fin (n + 1)) (t : ℝ) (y : Fin n → ℝ) :
    ‖chordInsert i t y‖ ^ 2 = t ^ 2 + ∑ j, y j ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succAbove _ i]
  simp only [chordInsert_apply_self, chordInsert_apply_other, Real.norm_eq_abs, sq_abs]

theorem chordInsert_sub {n : ℕ} (i : Fin (n + 1)) (s t : ℝ) (y : Fin n → ℝ) :
    chordInsert i s y - chordInsert i t y = EuclideanSpace.single i (s - t) := by
  ext j
  revert j
  refine (Fin.forall_iff_succAbove (P := fun j =>
    (chordInsert i s y - chordInsert i t y) j = EuclideanSpace.single i (s - t) j) i).2 ⟨?_, ?_⟩
  · simp [chordInsert_apply_self]
  · intro k
    simp [chordInsert_apply_other, Fin.succAbove_ne]

theorem chordInsert_isometry {n : ℕ} (i : Fin (n + 1)) (y : Fin n → ℝ) :
    Isometry (fun t => chordInsert i t y) := by
  apply isometry_iff_dist_eq.mpr
  intro s t
  rw [dist_eq_norm, chordInsert_sub, EuclideanSpace.norm_single, dist_eq_norm]

def chordHalfLength {n : ℕ} (ρ : ℝ) (y : Fin n → ℝ) : ℝ :=
  Real.sqrt (ρ ^ 2 - ∑ j, y j ^ 2)

theorem chordHalfLength_nonneg {n : ℕ} (ρ : ℝ) (y : Fin n → ℝ) : 0 ≤ chordHalfLength ρ y :=
  Real.sqrt_nonneg _

theorem chordHalfLength_sq {n : ℕ} {ρ : ℝ} {y : Fin n → ℝ} (hy : ∑ j, y j ^ 2 ≤ ρ ^ 2) :
    chordHalfLength ρ y ^ 2 = ρ ^ 2 - ∑ j, y j ^ 2 := Real.sq_sqrt (sub_nonneg.mpr hy)

theorem chordHalfLength_pos {n : ℕ} {ρ : ℝ} {y : Fin n → ℝ} :
    0 < chordHalfLength ρ y ↔ ∑ j, y j ^ 2 < ρ ^ 2 := by
  rw [chordHalfLength, Real.sqrt_pos, sub_pos]

theorem chordInsert_mem_ball_iff {n : ℕ} (i : Fin (n + 1)) {ρ : ℝ} (hρ : 0 < ρ)
    (t : ℝ) (y : Fin n → ℝ) :
    chordInsert i t y ∈ ball 0 ρ ↔ t ∈ Ioo (-chordHalfLength ρ y) (chordHalfLength ρ y) := by
  rw [mem_ball, dist_zero_right]
  have hn := norm_nonneg (chordInsert i t y)
  have hsq := chordInsert_norm_sq i t y
  have hh := chordHalfLength_nonneg ρ y
  constructor
  · intro ht
    have hy : ∑ j, y j ^ 2 < ρ ^ 2 := by nlinarith [sq_nonneg t]
    have hh2 := chordHalfLength_sq hy.le
    constructor <;> nlinarith
  · rintro ⟨hl, hu⟩
    have hp : 0 < chordHalfLength ρ y := by linarith
    have hh2 := chordHalfLength_sq (chordHalfLength_pos.mp hp).le
    nlinarith

theorem chordInsert_endpoint_mem {n : ℕ} (i : Fin (n + 1)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {y : Fin n → ℝ} (hy : ∑ j, y j ^ 2 ≤ ρ ^ 2) :
    chordInsert i (chordHalfLength ρ y) y ∈ closedBall 0 ρ ∧
      chordInsert i (-chordHalfLength ρ y) y ∈ closedBall 0 ρ := by
  have hh2 := chordHalfLength_sq hy
  constructor <;> rw [mem_closedBall, dist_zero_right]
  · nlinarith [chordInsert_norm_sq i (chordHalfLength ρ y) y, norm_nonneg (chordInsert i (chordHalfLength ρ y) y)]
  · nlinarith [chordInsert_norm_sq i (-chordHalfLength ρ y) y, norm_nonneg (chordInsert i (-chordHalfLength ρ y) y)]

def chordCoordinates {n : ℕ} (i : Fin (n + 1)) : CoordSpace (n + 1) ≃ᵐ ℝ × (Fin n → ℝ) :=
  (EuclideanSpace.measurableEquiv _).trans (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i)

theorem chordCoordinates_symm_apply {n : ℕ} (i : Fin (n + 1)) (p : ℝ × (Fin n → ℝ)) :
    (chordCoordinates i).symm p = chordInsert i p.1 p.2 := rfl

theorem chordCoordinates_preserving {n : ℕ} (i : Fin (n + 1)) :
    MeasurePreserving (chordCoordinates i) volume (volume.prod volume) :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).comp
    (EuclideanSpace.volume_preserving_measurableEquiv _)

theorem chordInsert_joint_measurable {n : ℕ} (i : Fin (n + 1)) :
    Measurable (fun p : ℝ × (Fin n → ℝ) => chordInsert i p.1 p.2) :=
  (chordCoordinates i).symm.measurable

theorem chordHalfLength_continuous {n : ℕ} (ρ : ℝ) : Continuous (chordHalfLength (n := n) ρ) := by
  exact Real.continuous_sqrt.comp (continuous_const.sub
    (continuous_finset_sum _ (fun j _ => (continuous_apply j).pow 2)))

end NCBall
