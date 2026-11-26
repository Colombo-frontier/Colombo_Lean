import NCBall.ChordQueries
import NCBall.LipschitzSampleModel
import NCBall.UpperSampling

/-! # The sample-function two-point oracle satisfies the first-order contract

The sample handle is independent of the ball point and coordinate. Its
random additive offset cancels between the two values. All Fubini steps
are justified using the square-integrable Lipschitz modulus.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped NNReal ENNReal BigOperators
namespace NCBall

abbrev StochasticChordSeed (n : ℕ) (Ξ : Type*) := Ξ × (CoordSpace (n + 1) × Fin (n + 1))

def stochasticChordLaw {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (n : ℕ) (ρ : ℝ) (hρ : 0 < ρ) : Measure (StochasticChordSeed n Ξ) :=
  μ.prod (chordSeedLaw n ρ hρ)

instance stochasticChordLaw_probability {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (n : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    IsProbabilityMeasure (stochasticChordLaw μ n ρ hρ) := by
  unfold stochasticChordLaw
  infer_instance

def stochasticChord {n : ℕ} {Ξ : Type*} (F : Ξ → CoordSpace (n + 1) → ℝ) (ρ : ℝ)
    (x : CoordSpace (n + 1)) (r : StochasticChordSeed n Ξ) : CoordSpace (n + 1) :=
  chordEstimate (F r.1) ρ x r.2

theorem stochasticChord_joint_measurable {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (F : Ξ → CoordSpace (n + 1) → ℝ)
    (hF : Measurable (fun p : CoordSpace (n + 1) × Ξ => F p.2 p.1)) (ρ : ℝ) :
    Measurable (fun p : CoordSpace (n + 1) × StochasticChordSeed n Ξ => stochasticChord F ρ p.1 p.2) := by
  have hm : Measurable (fun p : (CoordSpace (n + 1) × (Ξ × CoordSpace (n + 1))) × Fin (n + 1) =>
      chordEstimate (F p.1.2.1) ρ p.1.1 (p.1.2.2, p.2)) := by
    apply measurable_from_prod_countable
    intro i
    let T := CoordSpace (n + 1) × (Ξ × CoordSpace (n + 1))
    have hy : Measurable (fun p : T => chordSide i p.2.2) :=
      (chordSide_measurable i).comp measurable_snd.snd
    have hh := (chordHalfLength_continuous ρ).measurable.comp hy
    have hp := (chordInsert_joint_measurable i).comp (hh.prodMk hy)
    have hn := (chordInsert_joint_measurable i).comp (hh.neg.prodMk hy)
    have hfp := hF.comp ((measurable_fst.add hp).prodMk measurable_snd.fst)
    have hfn := hF.comp ((measurable_fst.add hn).prodMk measurable_snd.fst)
    change Measurable (fun p : T => ((n + 1 : ℝ) *
      ((F p.2.1 (p.1 + chordInsert i (chordHalfLength ρ (chordSide i p.2.2)) (chordSide i p.2.2)) -
        F p.2.1 (p.1 + chordInsert i (-chordHalfLength ρ (chordSide i p.2.2)) (chordSide i p.2.2))) /
        (2 * chordHalfLength ρ (chordSide i p.2.2)))) • EuclideanSpace.single i (1 : ℝ))
    exact (measurable_const.mul ((hfp.sub hfn).div (measurable_const.mul hh))).smul measurable_const
  have ht : Measurable (fun p : CoordSpace (n + 1) × StochasticChordSeed n Ξ =>
      ((p.1, (p.2.1, p.2.2.1)), p.2.2.2)) :=
    (measurable_fst.prodMk (measurable_snd.fst.prodMk measurable_snd.snd.fst)).prodMk measurable_snd.snd.snd
  have hfinal := hm.comp ht
  simpa only [Function.comp_def, Prod.mk.eta, stochasticChord] using hfinal

variable {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
  {f : CoordSpace (n + 1) → ℝ} {F : Ξ → CoordSpace (n + 1) → ℝ} {ℓ : Ξ → ℝ} {L : ℝ}

omit [IsProbabilityMeasure μ] in
theorem sample_chord_mean (hs : LipschitzSampleModel μ f F ℓ L) (ρ : ℝ)
    (x : CoordSpace (n + 1)) (w : CoordSpace (n + 1) × Fin (n + 1)) :
    (∫ ξ, chordEstimate (F ξ) ρ x w ∂μ) = chordEstimate f ρ x w := by
  simp_rw [chordEstimate_two_values]
  rw [integral_smul_const, integral_const_mul,
    integral_sub (hs.sample_integrable _) (hs.sample_integrable _), hs.sample_mean, hs.sample_mean]

omit [IsProbabilityMeasure μ] in
theorem stochasticChord_norm_le (hs : LipschitzSampleModel μ f F ℓ L) (ρ : ℝ)
    (x : CoordSpace (n + 1)) (r : StochasticChordSeed n Ξ) :
    ‖stochasticChord F ρ x r‖ ≤ (n + 1 : ℝ) * ℓ r.1 := by
  simpa only [stochasticChord, Real.coe_toNNReal _ (hs.modulus_nonneg r.1)] using
    chordEstimate_norm_le (hs.sample_lipschitz r.1) ρ x r.2

omit [IsProbabilityMeasure μ] in
theorem stochasticChord_memLp (hs : LipschitzSampleModel μ f F ℓ L)
    {ρ : ℝ} (hρ : 0 < ρ) (x : CoordSpace (n + 1)) :
    MemLp (stochasticChord F ρ x) 2 (stochasticChordLaw μ n ρ hρ) := by
  have hp : MeasurePreserving (Prod.fst : StochasticChordSeed n Ξ → Ξ)
      (stochasticChordLaw μ n ρ hρ) μ := ⟨measurable_fst, by simp [stochasticChordLaw]⟩
  have hb := (hs.modulus_memLp.comp_measurePreserving hp).const_mul (n + 1 : ℝ)
  have hm : Measurable (stochasticChord F ρ x) :=
    (stochasticChord_joint_measurable F hs.jointly_measurable ρ).comp
    (measurable_const.prodMk measurable_id)
  exact hb.mono' hm.aestronglyMeasurable (Eventually.of_forall (stochasticChord_norm_le hs ρ x))

theorem stochasticChord_mean (hs : LipschitzSampleModel μ f F ℓ L) (hL : 0 ≤ L)
    {ρ : ℝ} (hρ : 0 < ρ) (x : CoordSpace (n + 1)) :
    (∫ r, stochasticChord F ρ x r ∂stochasticChordLaw μ n ρ hρ) =
      gradient (ballAverage volume ρ hρ f) x := by
  have hi := (stochasticChord_memLp hs hρ x).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  rw [stochasticChordLaw, integral_prod_symm _ hi]
  simp_rw [stochasticChord, sample_chord_mean hs]
  exact chordEstimate_mean (hs.population_lipschitz hL) hρ x

theorem stochasticChord_second_moment (hs : LipschitzSampleModel μ f F ℓ L)
    {ρ : ℝ} (hρ : 0 < ρ) (x : CoordSpace (n + 1)) :
    (∫ r, ‖stochasticChord F ρ x r‖ ^ 2 ∂stochasticChordLaw μ n ρ hρ) ≤ (n + 1 : ℝ) * L ^ 2 := by
  have hi := (stochasticChord_memLp hs hρ x).norm.integrable_sq
  rw [stochasticChordLaw, integral_prod _ hi]
  calc
    _ ≤ ∫ ξ, (n + 1 : ℝ) * ℓ ξ ^ 2 ∂μ := by
      apply integral_mono hi.integral_prod_left (hs.modulus_square_integrable.const_mul _)
      intro ξ
      simpa only [stochasticChord, Real.coe_toNNReal _ (hs.modulus_nonneg ξ)] using
        chordEstimate_second_moment (hs.sample_lipschitz ξ) hρ x
    _ = (n + 1 : ℝ) * ∫ ξ, ℓ ξ ^ 2 ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hs.modulus_square_moment (by positivity)

theorem stochasticChord_oracle (hs : LipschitzSampleModel μ f F ℓ L) (hL : 0 ≤ L)
    {ρ : ℝ} (hρ : 0 < ρ) :
    OracleMoments (stochasticChordLaw μ n ρ hρ) (stochasticChord F ρ)
      (gradient (ballAverage volume ρ hρ f)) (Real.sqrt (n + 1 : ℝ) * L) where
  measurable := stochasticChord_joint_measurable F hs.jointly_measurable ρ
  mean_measurable := measurable_gradient _
  square_integrable := stochasticChord_memLp hs hρ
  mean := stochasticChord_mean hs hL hρ
  moment x := by
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (n + 1 : ℝ))]
    exact stochasticChord_second_moment hs hρ x

end NCBall
