import SecondOrder.AdaptiveChord

open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

theorem drawsSum_eq_sum {Ω E : Type*} [AddCommMonoid E] (X : Ω → E)
    (n : ℕ) (w : Draws Ω n) : drawsSum X n w = ∑ i : Fin n, X (drawsVector id n w i) := by
  induction n with
  | zero => simp [drawsSum]
  | succ n ih =>
    simp only [drawsSum, drawsVector, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, id_eq]
    rw [ih]

theorem robustBatch_eq_sample_average {Ω E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Ω → E) (m : ℕ) {R : ℕ} (hR : 0 < R) (ρ : ℝ) (w : Draws (Draws Ω m) R) :
    robustBatch X m hR ρ w = robustCenter hR
      (fun j => (m : ℝ)⁻¹ • ∑ i : Fin m, X (drawsVector id m (drawsVector id R w j) i)) (ρ/3) := by
  unfold robustBatch
  congr 1
  funext j
  rw [drawsVector_apply, drawsMean, drawsSum_eq_sum]

def chordSampleCall {Ω : Type*} {d : ℕ} (x y : Point d) (z : ℝ × Ω) : Ω × HvpQuery d :=
  (z.2,.hvp (x+z.1•(y-x)) (y-x))

theorem chordSampleCall_reply {Ω : Type*} {d : ℕ} (f : Ω → Point d → ℝ)
    (x y : Point d) (z : ℝ × Ω) :
    hvpReply f (chordSampleCall x y z).1 (chordSampleCall x y z).2 = randomLineHvp f x y z := rfl

abbrev AdaptiveChordSlot {A : Type*} {d : ℕ} (P : Parameters) (x y : A → Point d)
    (ρ δ : ℝ) (a : A) :=
  Fin (confidenceRepeats δ) × Fin (localBatchSize (chordVariance P (x a) (y a)) ρ)

def adaptiveChordCall {A Ω : Type*} {d : ℕ} (P : Parameters) (x y : A → Point d) (ρ δ : ℝ)
    (w : A × BatchTape (ℝ × Ω) (confidenceRepeats δ)) (i : AdaptiveChordSlot P x y ρ δ w.1) :
    Ω × HvpQuery d :=
  chordSampleCall (x w.1) (y w.1)
    (drawsVector id (localBatchSize (chordVariance P (x w.1) (y w.1)) ρ)
      (drawsVector id (confidenceRepeats δ)
        (w.2 (localBatchSize (chordVariance P (x w.1) (y w.1)) ρ)) i.1) i.2)

/-- The reported cost is exactly the number of permitted one-point HVP
queries whose replies occur in the estimator's batch averages. -/
theorem adaptiveChordCall_count {A : Type*} {d : ℕ} (P : Parameters) (x y : A → Point d)
    (ρ δ : ℝ) (a : A) : Fintype.card (AdaptiveChordSlot P x y ρ δ a) = adaptiveChordCost P x y ρ δ a := by
  simp [AdaptiveChordSlot, adaptiveChordCost, localQueryCount, Nat.mul_comm]

theorem adaptiveChord_eq_query_average {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
    {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ) (x y : A → Point d) (ρ δ : ℝ)
    (w : A × BatchTape (ℝ × Ω) (confidenceRepeats δ)) :
    adaptiveChord P f x y ρ δ w = robustCenter (confidenceRepeats_pos δ)
      (fun j => ((localBatchSize (chordVariance P (x w.1) (y w.1)) ρ : ℕ) : ℝ)⁻¹ •
        ∑ i : Fin (localBatchSize (chordVariance P (x w.1) (y w.1)) ρ),
          hvpReply f (adaptiveChordCall P x y ρ δ w (j,i)).1
            (adaptiveChordCall P x y ρ δ w (j,i)).2) (ρ/3) := by
  unfold adaptiveChord variableFreshEstimate
  rw [robustBatch_eq_sample_average]
  rfl

end
end SecondOrder
