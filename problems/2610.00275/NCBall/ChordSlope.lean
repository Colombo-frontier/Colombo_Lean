import NCBall.ChordIntegration

/-! # A chord slope is the conditional mean of the coordinate derivative -/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped NNReal InnerProductSpace
namespace NCBall

theorem chordInsert_affine {n : ℕ} (i : Fin (n + 1)) (t : ℝ) (y : Fin n → ℝ) :
    chordInsert i t y = chordInsert i 0 y + t • EuclideanSpace.single i 1 := by
  have hs := chordInsert_sub i t 0 y
  have he : EuclideanSpace.single i (t - 0) = t • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    by_cases hj : j = i <;> simp [hj, EuclideanSpace.single_apply, eq_comm]
  rw [he] at hs
  exact sub_eq_iff_eq_add.mp hs |>.trans (add_comm _ _)

theorem chordInsert_hasDerivAt {n : ℕ} (i : Fin (n + 1)) (t : ℝ) (y : Fin n → ℝ) :
    HasDerivAt (fun s => chordInsert i s y) (EuclideanSpace.single i 1) t := by
  have he : (fun s => chordInsert i s y) =
      fun s => chordInsert i 0 y + s • EuclideanSpace.single i 1 := funext (fun s => chordInsert_affine i s y)
  rw [he]
  simpa only [one_smul] using ((hasDerivAt_id t).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add
    (chordInsert i 0 y)

theorem chord_line_lipschitz {n : ℕ} {f : CoordSpace (n + 1) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (i : Fin (n + 1)) (x : CoordSpace (n + 1)) (y : Fin n → ℝ) :
    LipschitzWith L (fun t => f (x + chordInsert i t y)) := by
  simpa only [mul_one, Function.comp_def] using
    (hf.comp (isometry_add_left x).lipschitz).comp (chordInsert_isometry i y).lipschitz

theorem chord_line_deriv {n : ℕ} {f : CoordSpace (n + 1) → ℝ}
    (i : Fin (n + 1)) (x : CoordSpace (n + 1)) (y : Fin n → ℝ) (t : ℝ)
    (hf : DifferentiableAt ℝ f (x + chordInsert i t y)) :
    deriv (fun s => f (x + chordInsert i s y)) t = gradient f (x + chordInsert i t y) i := by
  have h := hf.hasGradientAt.hasFDerivAt.comp_hasDerivAt t ((chordInsert_hasDerivAt i t y).const_add x)
  simpa [InnerProductSpace.toDual_apply, EuclideanSpace.inner_single_right] using h.deriv

def chordSlope {n : ℕ} (f : CoordSpace (n + 1) → ℝ) (x : CoordSpace (n + 1))
    (i : Fin (n + 1)) (ρ : ℝ) (y : Fin n → ℝ) : ℝ :=
  (f (x + chordInsert i (chordHalfLength ρ y) y) -
    f (x + chordInsert i (-chordHalfLength ρ y) y)) / (2 * chordHalfLength ρ y)

theorem chordSlope_measurable {n : ℕ} {f : CoordSpace (n + 1) → ℝ} (hf : Continuous f)
    (x : CoordSpace (n + 1)) (i : Fin (n + 1)) (ρ : ℝ) :
    Measurable (chordSlope f x i ρ) := by
  have hp := (chordInsert_joint_measurable i).comp
    ((chordHalfLength_continuous (n := n) ρ).measurable.prodMk measurable_id)
  have hm := (chordInsert_joint_measurable i).comp
    ((chordHalfLength_continuous (n := n) ρ).measurable.neg.prodMk measurable_id)
  exact ((hf.measurable.comp (measurable_const.add hp)).sub
    (hf.measurable.comp (measurable_const.add hm))).div
      (measurable_const.mul (chordHalfLength_continuous ρ).measurable)

theorem chordSlope_abs_le {n : ℕ} {f : CoordSpace (n + 1) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (x : CoordSpace (n + 1)) (i : Fin (n + 1)) (ρ : ℝ) (y : Fin n → ℝ) :
    |chordSlope f x i ρ y| ≤ L := by
  have hh := chordHalfLength_nonneg ρ y
  by_cases hz : chordHalfLength ρ y = 0
  · simp [chordSlope, hz, L.coe_nonneg]
  · have hp : 0 < 2 * chordHalfLength ρ y := by positivity
    rw [chordSlope, abs_div, abs_of_pos hp, div_le_iff₀ hp]
    have hl := (chord_line_lipschitz hf i x y).norm_sub_le (chordHalfLength ρ y) (-chordHalfLength ρ y)
    simpa only [Real.norm_eq_abs, sub_neg_eq_add, ← two_mul, abs_of_nonneg (by positivity :
      0 ≤ 2 * chordHalfLength ρ y)] using hl

theorem chordSlope_eq_integral_gradient {n : ℕ} {f : CoordSpace (n + 1) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (x : CoordSpace (n + 1)) (i : Fin (n + 1)) (ρ : ℝ) :
    ∀ᵐ y : Fin n → ℝ, chordSlope f x i ρ y = (2 * chordHalfLength ρ y)⁻¹ *
      ∫ t in (-chordHalfLength ρ y)..(chordHalfLength ρ y), gradient f (x + chordInsert i t y) i := by
  filter_upwards [ae_chord_differentiable hf i x] with y hy
  have he : (fun t => deriv (fun s => f (x + chordInsert i s y)) t) =ᵐ[volume]
      (fun t => gradient f (x + chordInsert i t y) i) :=
    hy.mono (fun t ht => chord_line_deriv i x y t ht)
  have hi : (∫ t in (-chordHalfLength ρ y)..(chordHalfLength ρ y),
      deriv (fun s => f (x + chordInsert i s y)) t) =
      ∫ t in (-chordHalfLength ρ y)..(chordHalfLength ρ y), gradient f (x + chordInsert i t y) i :=
    intervalIntegral.integral_congr_ae (he.mono (fun _ ht _ => ht))
  rw [← hi,
    integral_deriv_of_lipschitz (chord_line_lipschitz hf i x y)]
  simp only [chordSlope, div_eq_mul_inv, mul_comm]

end NCBall
