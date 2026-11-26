import NCBall.ZerothOrderProcess

/-! # Fresh handles and independence from the current sample function -/

noncomputable section
open MeasureTheory
namespace NCBall

theorem stochastic_sample_geometry_prefix_law {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ) :
    MeasurePreserving (fun w : UpperRandomness (StochasticChordSeed n Ξ) =>
      ((fun i : Fin K => (w.2 i.val).1), (fun i : Fin K => (w.2 i.val).2)))
      (upperPoolLaw (stochasticChordLaw μ n ρ hρ))
      ((Measure.pi (fun _ : Fin K => μ)).prod (Measure.pi (fun _ : Fin K => chordSeedLaw n ρ hρ))) := by
  have hp : MeasurePreserving (Prod.snd : UpperRandomness (StochasticChordSeed n Ξ) →
      (ℕ → StochasticChordSeed n Ξ)) (upperPoolLaw (stochasticChordLaw μ n ρ hρ))
      (Measure.infinitePi (fun _ : ℕ => stochasticChordLaw μ n ρ hρ)) :=
    ⟨measurable_snd, by simp [upperPoolLaw]⟩
  exact (measurePreserving_arrowProdEquivProdArrow Ξ (CoordSpace (n + 1) × Fin (n + 1)) (Fin K)
    (fun _ => μ) (fun _ => chordSeedLaw n ρ hρ)).comp
      ((poolPrefix_law (stochasticChordLaw μ n ρ hρ) K).comp hp)

theorem stochastic_handle_prefix_law {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ) :
    MeasurePreserving (fun w : UpperRandomness (StochasticChordSeed n Ξ) =>
      fun i : Fin K => (w.2 i.val).1)
      (upperPoolLaw (stochasticChordLaw μ n ρ hρ)) (Measure.pi (fun _ : Fin K => μ)) := by
  have hp : MeasurePreserving (Prod.snd : UpperRandomness (StochasticChordSeed n Ξ) →
      (ℕ → StochasticChordSeed n Ξ)) (upperPoolLaw (stochasticChordLaw μ n ρ hρ))
      (Measure.infinitePi (fun _ : ℕ => stochasticChordLaw μ n ρ hρ)) :=
    ⟨measurable_snd, by simp [upperPoolLaw]⟩
  have hm : MeasurePreserving (Prod.fst : StochasticChordSeed n Ξ → Ξ)
      (stochasticChordLaw μ n ρ hρ) μ := ⟨measurable_fst, by simp [stochasticChordLaw]⟩
  have hf := measurePreserving_pi (fun _ : Fin K => stochasticChordLaw μ n ρ hρ)
    (fun _ : Fin K => μ) (fun _ => hm)
  exact hf.comp ((poolPrefix_law (stochasticChordLaw μ n ρ hρ) K).comp hp)

theorem zerothPlusQuery_current_sample_invariant {n : ℕ} {Ξ : Type*}
    (ρ D : ℝ) (hD : 0 ≤ D) (α : ℝ) (F : Ξ → CoordSpace (n + 1) → ℝ)
    (x₀ : CoordSpace (n + 1)) (w : UpperRandomness (StochasticChordSeed n Ξ)) (t : ℕ) (ξ : Ξ) :
    zerothPlusQuery ρ D hD α F x₀ (w.1, Function.update w.2 t (ξ, (w.2 t).2)) t =
      zerothPlusQuery ρ D hD α F x₀ w t := by
  unfold zerothPlusQuery
  rw [upperLocation_noise_refresh D hD α (stochasticChord F ρ) x₀ w.1 w.2 t (ξ, (w.2 t).2) le_rfl]
  simp only [Prod.snd, Function.update_self]

theorem zerothMinusQuery_current_sample_invariant {n : ℕ} {Ξ : Type*}
    (ρ D : ℝ) (hD : 0 ≤ D) (α : ℝ) (F : Ξ → CoordSpace (n + 1) → ℝ)
    (x₀ : CoordSpace (n + 1)) (w : UpperRandomness (StochasticChordSeed n Ξ)) (t : ℕ) (ξ : Ξ) :
    zerothMinusQuery ρ D hD α F x₀ (w.1, Function.update w.2 t (ξ, (w.2 t).2)) t =
      zerothMinusQuery ρ D hD α F x₀ w t := by
  unfold zerothMinusQuery
  rw [upperLocation_noise_refresh D hD α (stochasticChord F ρ) x₀ w.1 w.2 t (ξ, (w.2 t).2) le_rfl]
  simp only [Prod.snd, Function.update_self]

end NCBall
