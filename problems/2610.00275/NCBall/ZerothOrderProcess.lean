import NCBall.StochasticChord

/-! # The clipped process as two scalar queries per fresh sample -/

noncomputable section
open MeasureTheory Set Metric
open scoped BigOperators unitInterval
namespace NCBall

theorem chordQuery_signed_measurable {n : ℕ} (ρ sign : ℝ) :
    Measurable (fun p : CoordSpace (n + 1) × (CoordSpace (n + 1) × Fin (n + 1)) =>
      p.1 + if ∑ j, (chordSide p.2.2 p.2.1 j) ^ 2 ≤ ρ ^ 2 then
        chordInsert p.2.2 (sign * chordHalfLength ρ (chordSide p.2.2 p.2.1)) (chordSide p.2.2 p.2.1) else 0) := by
  have hm : Measurable (fun p : (CoordSpace (n + 1) × CoordSpace (n + 1)) × Fin (n + 1) =>
      p.1.1 + if ∑ j, (chordSide p.2 p.1.2 j) ^ 2 ≤ ρ ^ 2 then
        chordInsert p.2 (sign * chordHalfLength ρ (chordSide p.2 p.1.2)) (chordSide p.2 p.1.2) else 0) := by
    apply measurable_from_prod_countable
    intro i
    have hy : Measurable (fun p : CoordSpace (n + 1) × CoordSpace (n + 1) => chordSide i p.2) :=
      (chordSide_measurable i).comp measurable_snd
    have hh := (chordHalfLength_continuous ρ).measurable.comp hy
    have hsq : Measurable (fun p : CoordSpace (n + 1) × CoordSpace (n + 1) =>
        ∑ j, (chordSide i p.2 j) ^ 2) :=
      Finset.measurable_sum _ (fun j _ => ((measurable_pi_apply j).comp hy).pow_const 2)
    exact measurable_fst.add (Measurable.ite (measurableSet_le hsq measurable_const)
      ((chordInsert_joint_measurable i).comp ((measurable_const.mul hh).prodMk hy)) measurable_const)
  have ht : Measurable (fun p : CoordSpace (n + 1) × (CoordSpace (n + 1) × Fin (n + 1)) =>
      ((p.1, p.2.1), p.2.2)) :=
    (measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd
  exact hm.comp ht

theorem chordQueryPlus_joint_measurable {n : ℕ} (ρ : ℝ) :
    Measurable (fun p : CoordSpace (n + 1) × (CoordSpace (n + 1) × Fin (n + 1)) =>
      chordQueryPlus ρ p.1 p.2) := by
  simpa only [one_mul, chordQueryPlus] using chordQuery_signed_measurable (n := n) ρ 1

theorem chordQueryMinus_joint_measurable {n : ℕ} (ρ : ℝ) :
    Measurable (fun p : CoordSpace (n + 1) × (CoordSpace (n + 1) × Fin (n + 1)) =>
      chordQueryMinus ρ p.1 p.2) := by
  simpa only [neg_one_mul, chordQueryMinus] using chordQuery_signed_measurable (n := n) ρ (-1)

def zerothPlusQuery {n : ℕ} {Ξ : Type*} (ρ D : ℝ) (hD : 0 ≤ D) (α : ℝ)
    (F : Ξ → CoordSpace (n + 1) → ℝ) (x₀ : CoordSpace (n + 1))
    (w : UpperRandomness (StochasticChordSeed n Ξ)) (t : ℕ) : CoordSpace (n + 1) :=
  chordQueryPlus ρ (upperLocation D hD α (stochasticChord F ρ) x₀ w.1 w.2 t) (w.2 t).2

def zerothMinusQuery {n : ℕ} {Ξ : Type*} (ρ D : ℝ) (hD : 0 ≤ D) (α : ℝ)
    (F : Ξ → CoordSpace (n + 1) → ℝ) (x₀ : CoordSpace (n + 1))
    (w : UpperRandomness (StochasticChordSeed n Ξ)) (t : ℕ) : CoordSpace (n + 1) :=
  chordQueryMinus ρ (upperLocation D hD α (stochasticChord F ρ) x₀ w.1 w.2 t) (w.2 t).2

theorem zerothPlusQuery_measurable {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (ρ D : ℝ) (hD : 0 ≤ D) (α : ℝ) (F : Ξ → CoordSpace (n + 1) → ℝ)
    (hF : Measurable (fun p : CoordSpace (n + 1) × Ξ => F p.2 p.1))
    (x₀ : CoordSpace (n + 1)) (t : ℕ) : Measurable (fun w => zerothPlusQuery ρ D hD α F x₀ w t) :=
  (chordQueryPlus_joint_measurable ρ).comp
    ((upperLocation_measurable D hD α (stochasticChord F ρ) (stochasticChord_joint_measurable F hF ρ) x₀ t).prodMk
      (((measurable_pi_apply t).comp measurable_snd).snd))

theorem zerothMinusQuery_measurable {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (ρ D : ℝ) (hD : 0 ≤ D) (α : ℝ) (F : Ξ → CoordSpace (n + 1) → ℝ)
    (hF : Measurable (fun p : CoordSpace (n + 1) × Ξ => F p.2 p.1))
    (x₀ : CoordSpace (n + 1)) (t : ℕ) : Measurable (fun w => zerothMinusQuery ρ D hD α F x₀ w t) :=
  (chordQueryMinus_joint_measurable ρ).comp
    ((upperLocation_measurable D hD α (stochasticChord F ρ) (stochasticChord_joint_measurable F hF ρ) x₀ t).prodMk
      (((measurable_pi_apply t).comp measurable_snd).snd))

theorem upperEstimate_two_scalar_values {n : ℕ} {Ξ : Type*}
    (ρ D : ℝ) (hD : 0 ≤ D) (α : ℝ) (F : Ξ → CoordSpace (n + 1) → ℝ)
    (x₀ : CoordSpace (n + 1)) (w : UpperRandomness (StochasticChordSeed n Ξ)) (t : ℕ) :
    upperEstimate D hD α (stochasticChord F ρ) x₀ w.1 w.2 t =
      ((n + 1 : ℝ) / (2 * chordHalfLength ρ (chordSide (w.2 t).2.2 (w.2 t).2.1)) *
        (F (w.2 t).1 (zerothPlusQuery ρ D hD α F x₀ w t) -
          F (w.2 t).1 (zerothMinusQuery ρ D hD α F x₀ w t))) • EuclideanSpace.single (w.2 t).2.2 1 :=
  chordEstimate_two_values (F (w.2 t).1) ρ _ (w.2 t).2

end NCBall
