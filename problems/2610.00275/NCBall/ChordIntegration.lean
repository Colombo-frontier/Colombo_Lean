import NCBall.ChordGeometry

/-! # Fubini decomposition of a Euclidean ball into coordinate chords -/

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped NNReal
namespace NCBall

theorem integral_ball_chords {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin (n + 1)) {ρ : ℝ} (hρ : 0 < ρ) (g : CoordSpace (n + 1) → F)
    (hg : IntegrableOn g (ball 0 ρ) volume) :
    (∫ z in ball 0 ρ, g z) = ∫ y : Fin n → ℝ,
      ∫ t in Ioo (-chordHalfLength ρ y) (chordHalfLength ρ y), g (chordInsert i t y) := by
  have hi : Integrable ((ball (0 : CoordSpace (n + 1)) ρ).indicator g) :=
    (integrable_indicator_iff isOpen_ball.measurableSet).2 hg
  have hb := MeasurePreserving.symm (chordCoordinates i) (chordCoordinates_preserving i)
  have hp := (hb.integrable_comp_emb (chordCoordinates i).symm.measurableEmbedding).2 hi
  dsimp only [Function.comp_def] at hp
  rw [← integral_indicator isOpen_ball.measurableSet,
    ← hb.integral_comp', integral_prod_symm _ hp]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards [] with t
  change (ball (0 : CoordSpace (n + 1)) ρ).indicator g (chordInsert i t y) =
    (Ioo (-chordHalfLength ρ y) (chordHalfLength ρ y)).indicator (fun s => g (chordInsert i s y)) t
  by_cases ht : t ∈ Ioo (-chordHalfLength ρ y) (chordHalfLength ρ y)
  · rw [Set.indicator_of_mem ((chordInsert_mem_ball_iff i hρ t y).2 ht), Set.indicator_of_mem ht]
  · rw [Set.indicator_of_not_mem (fun hz => ht ((chordInsert_mem_ball_iff i hρ t y).1 hz)),
      Set.indicator_of_not_mem ht]

theorem integral_ball_chords_interval {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin (n + 1)) {ρ : ℝ} (hρ : 0 < ρ) (g : CoordSpace (n + 1) → F)
    (hg : IntegrableOn g (ball 0 ρ) volume) :
    (∫ z in ball 0 ρ, g z) = ∫ y : Fin n → ℝ,
      ∫ t in (-chordHalfLength ρ y)..(chordHalfLength ρ y), g (chordInsert i t y) := by
  rw [integral_ball_chords i hρ g hg]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [intervalIntegral.integral_of_le (by linarith [chordHalfLength_nonneg ρ y]),
    integral_Ioc_eq_integral_Ioo]

theorem ae_chord_differentiable {n : ℕ} {f : CoordSpace (n + 1) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (i : Fin (n + 1)) (x : CoordSpace (n + 1)) :
    ∀ᵐ y : Fin n → ℝ, ∀ᵐ t : ℝ, DifferentiableAt ℝ f (x + chordInsert i t y) := by
  have hd : ∀ᵐ z, DifferentiableAt ℝ f (x + z) :=
    (eventually_add_left_iff volume x).2 (hf.ae_differentiableAt (μ := volume))
  have hb := MeasurePreserving.symm (chordCoordinates i) (chordCoordinates_preserving i)
  have hp := hb.quasiMeasurePreserving.ae hd
  exact ae_ae_of_ae_prod (measurePreserving_swap.quasiMeasurePreserving.ae hp)

end NCBall
