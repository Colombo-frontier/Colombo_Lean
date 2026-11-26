import SampleReuse.ReverseStickThirdEmbeddingEnergy

/-! Dimension-independent moment bounds for ordered distinct-index scores. -/

open SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section
variable {ι : Type*} [Fintype ι]

def orderedBernoulliScore (n : ℕ) (p : ι → ℝ) (a : Fin n → ι → ℝ)
    (w : ι → Bool) : ℝ :=
  ∑ e : Fin n ↪ ι, (∏ j, a j (e j)) *
    scoreMonomial (fun i => binaryScore (p i)) (embeddingSupport e) w

/-- The multiplicity cost depends on derivative order alone: it is 4 at
order two and 27 at order three, independently of the number of gates. -/
theorem orderedBernoulliScore_square_mean_le
    (n : ℕ) (p : ι → ℝ) (a : Fin n → ι → ℝ)
    (hp0 : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) :
    pmfMean (bernoulliProduct p (fun i => (hp0 i).le) (fun i => (hp1 i).le))
      (fun w => orderedBernoulliScore n p a w ^ 2) ≤
      (n ^ n : ℕ) * ∏ j, bernoulliFisherEnergy p (a j) := by
  have hh := scoreFamily_square_mean_le
    (fun i => binaryPMF (p i) (hp0 i).le (hp1 i).le)
    (fun i => binaryScore (p i)) (fun i => binaryScore_mean (hp0 i) (hp1 i))
    (@embeddingSupport ι n) (fun e => ∏ j, a j (e j)) (n ^ n)
    (embeddingSupport_fiber_card n)
  have hh' : pmfMean (bernoulliProduct p (fun i => (hp0 i).le) (fun i => (hp1 i).le))
      (fun w => orderedBernoulliScore n p a w ^ 2) ≤
      (n ^ n : ℕ) * ∑ e : Fin n ↪ ι, (∏ j, a j (e j)) ^ 2 *
        ∏ i ∈ embeddingSupport e, (1 / (p i * (1 - p i))) := by
    simpa only [orderedBernoulliScore, bernoulliProduct,
      binaryScore_second_moment (hp0 _) (hp1 _)] using hh
  exact hh'.trans (mul_le_mul_of_nonneg_left
    (embedding_fisher_energy_le n p a hp0 hp1) (Nat.cast_nonneg _))

theorem orderedBernoulliScore_abs_mean_le
    (n : ℕ) (p : ι → ℝ) (a : Fin n → ι → ℝ)
    (hp0 : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) :
    pmfMean (bernoulliProduct p (fun i => (hp0 i).le) (fun i => (hp1 i).le))
      (fun w => |orderedBernoulliScore n p a w|) ≤
      Real.sqrt ((n ^ n : ℕ) * ∏ j, bernoulliFisherEnergy p (a j)) := by
  exact (pmfMean_abs_le_sqrt _ (orderedBernoulliScore n p a)).trans
    (Real.sqrt_le_sqrt (orderedBernoulliScore_square_mean_le n p a hp0 hp1))

end
end SampleReuse
