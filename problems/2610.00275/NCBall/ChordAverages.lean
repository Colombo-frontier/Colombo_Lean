import NCBall.ChordSlope
import NCBall.IntervalMoment

/-! # Integrating chord slopes over a ball -/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped NNReal
namespace NCBall

def chordSide {n : ℕ} (i : Fin (n + 1)) (z : CoordSpace (n + 1)) : Fin n → ℝ :=
  (chordCoordinates i z).2

theorem chordSide_measurable {n : ℕ} (i : Fin (n + 1)) : Measurable (chordSide i) :=
  (chordCoordinates i).measurable.snd

theorem chordSide_insert {n : ℕ} (i : Fin (n + 1)) (t : ℝ) (y : Fin n → ℝ) :
    chordSide i (chordInsert i t y) = y := by
  funext j
  exact chordInsert_apply_other i t y j

theorem integrableOn_ball_of_bounded {n : ℕ} {g : CoordSpace n → ℝ}
    (hg : Measurable g) {B : ℝ} (hb : ∀ z, ‖g z‖ ≤ B) (ρ : ℝ) :
    IntegrableOn g (ball 0 ρ) volume := by
  have hc : IntegrableOn (fun _ : CoordSpace n => B) (ball 0 ρ) volume :=
    integrableOn_const.mpr (Or.inr measure_ball_lt_top)
  exact hc.mono' hg.aestronglyMeasurable.restrict (Eventually.of_forall hb)

theorem chord_indicator_integral {n : ℕ} (i : Fin (n + 1)) {ρ : ℝ} (hρ : 0 < ρ)
    (g : CoordSpace (n + 1) → ℝ) (y : Fin n → ℝ) :
    (∫ t : ℝ, (ball 0 ρ).indicator g (chordInsert i t y)) =
      ∫ t in (-chordHalfLength ρ y)..(chordHalfLength ρ y), g (chordInsert i t y) := by
  rw [intervalIntegral.integral_of_le (by linarith [chordHalfLength_nonneg ρ y]),
    integral_Ioc_eq_integral_Ioo, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Ioo (-chordHalfLength ρ y) (chordHalfLength ρ y)
  · rw [Set.indicator_of_mem ((chordInsert_mem_ball_iff i hρ t y).2 ht), Set.indicator_of_mem ht]
  · rw [Set.indicator_of_not_mem (fun hz => ht ((chordInsert_mem_ball_iff i hρ t y).1 hz)),
      Set.indicator_of_not_mem ht]

theorem integrable_ball_chords {n : ℕ} (i : Fin (n + 1)) {ρ : ℝ} (hρ : 0 < ρ)
    (g : CoordSpace (n + 1) → ℝ) (hg : IntegrableOn g (ball 0 ρ) volume) :
    Integrable (fun y : Fin n → ℝ =>
      ∫ t in (-chordHalfLength ρ y)..(chordHalfLength ρ y), g (chordInsert i t y)) := by
  have hi : Integrable ((ball (0 : CoordSpace (n + 1)) ρ).indicator g) :=
    (integrable_indicator_iff isOpen_ball.measurableSet).2 hg
  have hb := MeasurePreserving.symm (chordCoordinates i) (chordCoordinates_preserving i)
  have hp := (hb.integrable_comp_emb (chordCoordinates i).symm.measurableEmbedding).2 hi
  have hir := hp.integral_prod_right
  simpa only [Function.comp_apply, chordCoordinates_symm_apply, chord_indicator_integral i hρ] using hir

theorem coordinate_gradient_measurable {n : ℕ} (f : CoordSpace n → ℝ) (x : CoordSpace n)
    (i : Fin n) : Measurable (fun z => gradient f (x + z) i) :=
  (continuous_apply i).measurable.comp
    ((measurable_gradient f).comp (measurable_const.add measurable_id))

theorem coordinate_gradient_norm_le {n : ℕ} {f : CoordSpace n → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (i : Fin n) (x : CoordSpace n) : ‖gradient f x i‖ ≤ L :=
  (PiLp.norm_apply_le (gradient f x) i).trans (norm_gradient_le_of_lipschitz hf x)

theorem chordSlope_length_mul {n : ℕ} {f : CoordSpace (n + 1) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (x : CoordSpace (n + 1)) (i : Fin (n + 1)) (ρ : ℝ) :
    ∀ᵐ y : Fin n → ℝ, (2 * chordHalfLength ρ y) * chordSlope f x i ρ y =
      ∫ t in (-chordHalfLength ρ y)..(chordHalfLength ρ y), gradient f (x + chordInsert i t y) i := by
  filter_upwards [chordSlope_eq_integral_gradient hf x i ρ] with y hy
  by_cases hh : chordHalfLength ρ y = 0
  · simp [hh]
  · rw [hy]
    field_simp

theorem chordSlope_integral_ball {n : ℕ} {f : CoordSpace (n + 1) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (x : CoordSpace (n + 1)) (i : Fin (n + 1)) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ z in ball 0 ρ, chordSlope f x i ρ (chordSide i z)) =
      ∫ z in ball 0 ρ, gradient f (x + z) i := by
  have hiq := integrableOn_ball_of_bounded
    ((chordSlope_measurable hf.continuous x i ρ).comp (chordSide_measurable i))
    (fun z => by simpa only [Real.norm_eq_abs] using chordSlope_abs_le hf x i ρ (chordSide i z)) ρ
  have hig := integrableOn_ball_of_bounded (coordinate_gradient_measurable f x i)
    (fun z => coordinate_gradient_norm_le hf i (x + z)) ρ
  dsimp only [Function.comp_def] at hiq
  rw [integral_ball_chords_interval i hρ _ hiq, integral_ball_chords_interval i hρ _ hig]
  apply integral_congr_ae
  filter_upwards [chordSlope_length_mul hf x i ρ] with y hy
  simpa only [chordSide_insert, intervalIntegral.integral_const, sub_neg_eq_add,
    ← two_mul, smul_eq_mul] using hy

theorem chordSlope_square_fiber {n : ℕ} {f : CoordSpace (n + 1) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (x : CoordSpace (n + 1)) (i : Fin (n + 1)) (ρ : ℝ) :
    ∀ᵐ y : Fin n → ℝ, (2 * chordHalfLength ρ y) * (chordSlope f x i ρ y) ^ 2 ≤
      ∫ t in (-chordHalfLength ρ y)..(chordHalfLength ρ y), (gradient f (x + chordInsert i t y) i) ^ 2 := by
  filter_upwards [chordSlope_length_mul hf x i ρ] with y hy
  exact interval_average_square_le
    ((coordinate_gradient_measurable f x i).comp (chordInsert_isometry i y).continuous.measurable)
    (fun t => coordinate_gradient_norm_le hf i (x + chordInsert i t y))
    (chordHalfLength_nonneg ρ y) hy.symm

theorem chordSlope_square_integral_ball {n : ℕ} {f : CoordSpace (n + 1) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (x : CoordSpace (n + 1)) (i : Fin (n + 1)) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ z in ball 0 ρ, (chordSlope f x i ρ (chordSide i z)) ^ 2) ≤
      ∫ z in ball 0 ρ, (gradient f (x + z) i) ^ 2 := by
  have hiq := integrableOn_ball_of_bounded
    (((chordSlope_measurable hf.continuous x i ρ).comp (chordSide_measurable i)).pow_const 2)
    (B := (L : ℝ) ^ 2) (fun z => by
      rw [norm_pow, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (chordSlope_abs_le hf x i ρ _) 2) ρ
  have hig := integrableOn_ball_of_bounded ((coordinate_gradient_measurable f x i).pow_const 2)
    (B := (L : ℝ) ^ 2) (fun z => by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (coordinate_gradient_norm_le hf i (x + z)) 2) ρ
  dsimp only [Function.comp_def] at hiq
  rw [integral_ball_chords_interval i hρ _ hiq, integral_ball_chords_interval i hρ _ hig]
  apply integral_mono_ae (integrable_ball_chords i hρ _ hiq) (integrable_ball_chords i hρ _ hig)
  filter_upwards [chordSlope_square_fiber hf x i ρ] with y hy
  simpa only [chordSide_insert, intervalIntegral.integral_const, sub_neg_eq_add,
    ← two_mul, smul_eq_mul] using hy

theorem ballLaw_integral {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ℝ) (hρ : 0 < ρ) (g : CoordSpace n → F) :
    (∫ z, g z ∂ballLaw volume ρ hρ) = (volume (ball (0 : CoordSpace n) ρ)).toReal⁻¹ •
      ∫ z in ball 0 ρ, g z := by
  simpa only [ballAverage, zero_add] using ballAverage_eq_setIntegral volume ρ hρ g 0

theorem chordSlope_mean {n : ℕ} {f : CoordSpace (n + 1) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (x : CoordSpace (n + 1)) (i : Fin (n + 1)) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ z, chordSlope f x i ρ (chordSide i z) ∂ballLaw volume ρ hρ) =
      gradient (ballAverage volume ρ hρ f) x i := by
  rw [ballAverage_gradient volume ρ hρ hf x]
  have he : (∫ z, gradient f (x + z) ∂ballLaw volume ρ hρ) i =
      ∫ z, gradient f (x + z) i ∂ballLaw volume ρ hρ :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (n + 1) => ℝ) i).integral_comp_comm
      (ball_gradient_integrable volume ρ hρ hf x)).symm
  rw [he, ballLaw_integral, ballLaw_integral, chordSlope_integral_ball hf x i hρ]

theorem chordSlope_second_moment {n : ℕ} {f : CoordSpace (n + 1) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (x : CoordSpace (n + 1)) (i : Fin (n + 1)) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ z, (chordSlope f x i ρ (chordSide i z)) ^ 2 ∂ballLaw volume ρ hρ) ≤
      ∫ z, (gradient f (x + z) i) ^ 2 ∂ballLaw volume ρ hρ := by
  rw [ballLaw_integral, ballLaw_integral, smul_eq_mul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (chordSlope_square_integral_ball hf x i hρ) (by positivity)

end NCBall
