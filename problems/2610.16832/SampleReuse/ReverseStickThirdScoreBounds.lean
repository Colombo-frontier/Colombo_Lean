import SampleReuse.ReverseStickThirdCombinatorics

/-! The normalized third likelihood score and its uniform first-moment bound. -/

open SecondOrder
open scoped BigOperators Classical
namespace SampleReuse
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem orderedBernoulliScore_two (p a b : ι → ℝ) (w : ι → Bool) :
    orderedBernoulliScore 2 p ![a, b] w =
      (∑ i, a i * binaryScore (p i) (w i)) *
      (∑ i, b i * binaryScore (p i) (w i)) -
      ∑ i, (a i * binaryScore (p i) (w i)) * (b i * binaryScore (p i) (w i)) := by
  rw [orderedBernoulliScore_eq_coordinateProduct]
  have he : (fun j i => ![a, b] j i * binaryScore (p i) (w i)) =
      ![(fun i => a i * binaryScore (p i) (w i)),
        (fun i => b i * binaryScore (p i) (w i))] := by
    funext j i
    fin_cases j <;> rfl
  rw [he, orderedCoordinateProduct_two]

theorem orderedBernoulliScore_three (p a b c : ι → ℝ) (w : ι → Bool) :
    orderedBernoulliScore 3 p ![a, b, c] w =
      (∑ i, a i * binaryScore (p i) (w i)) *
      (∑ i, b i * binaryScore (p i) (w i)) *
      (∑ i, c i * binaryScore (p i) (w i)) -
      (∑ i, (a i * binaryScore (p i) (w i)) * (b i * binaryScore (p i) (w i))) *
      (∑ i, c i * binaryScore (p i) (w i)) -
      (∑ i, (a i * binaryScore (p i) (w i)) * (c i * binaryScore (p i) (w i))) *
      (∑ i, b i * binaryScore (p i) (w i)) -
      (∑ i, (b i * binaryScore (p i) (w i)) * (c i * binaryScore (p i) (w i))) *
      (∑ i, a i * binaryScore (p i) (w i)) +
      2 * ∑ i, (a i * binaryScore (p i) (w i)) *
        (b i * binaryScore (p i) (w i)) * (c i * binaryScore (p i) (w i)) := by
  rw [orderedBernoulliScore_eq_coordinateProduct]
  have he : (fun j i => ![a, b, c] j i * binaryScore (p i) (w i)) =
      ![(fun i => a i * binaryScore (p i) (w i)),
        (fun i => b i * binaryScore (p i) (w i)),
        (fun i => c i * binaryScore (p i) (w i))] := by
    funext j i
    fin_cases j <;> rfl
  rw [he, orderedCoordinateProduct_three]

/-- Cancellation of repeated indices is exact, before applying any estimate. -/
theorem bernoulliThirdScore_decomposition (p a b c ab ac bc abc : ι → ℝ)
    (w : ι → Bool) :
    bernoulliThirdScore p a b c ab ac bc abc w =
      bernoulliScoreSum p abc w + orderedBernoulliScore 2 p ![ab, c] w +
      orderedBernoulliScore 2 p ![ac, b] w + orderedBernoulliScore 2 p ![bc, a] w +
      orderedBernoulliScore 3 p ![a, b, c] w := by
  simp only [bernoulliThirdScore, normalizedThirdScore, bernoulliScoreSum,
    orderedBernoulliScore_two, orderedBernoulliScore_three, Finset.sum_add_distrib]
  ring

/-- A dimension-free third-score bound. The cubic constant sqrt(27) comes
from a deliberately non-sharp support-multiplicity estimate. -/
theorem bernoulliThirdScore_abs_mean_le
    (p a b c ab ac bc abc : ι → ℝ) (hp0 : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) :
    pmfMean (bernoulliProduct p (fun i => (hp0 i).le) (fun i => (hp1 i).le))
      (fun w => |bernoulliThirdScore p a b c ab ac bc abc w|) ≤
      2 * (∑ i, |abc i|) +
      Real.sqrt (4 * (bernoulliFisherEnergy p ab * bernoulliFisherEnergy p c)) +
      Real.sqrt (4 * (bernoulliFisherEnergy p ac * bernoulliFisherEnergy p b)) +
      Real.sqrt (4 * (bernoulliFisherEnergy p bc * bernoulliFisherEnergy p a)) +
      Real.sqrt (27 * (bernoulliFisherEnergy p a * bernoulliFisherEnergy p b *
        bernoulliFisherEnergy p c)) := by
  let P := bernoulliProduct p (fun i => (hp0 i).le) (fun i => (hp1 i).le)
  have h1 := bernoulliScoreSum_abs_mean_le_sum p abc hp0 hp1
  have h2 := orderedBernoulliScore_abs_mean_le 2 p ![ab, c] hp0 hp1
  have h3 := orderedBernoulliScore_abs_mean_le 2 p ![ac, b] hp0 hp1
  have h4 := orderedBernoulliScore_abs_mean_le 2 p ![bc, a] hp0 hp1
  have h5 := orderedBernoulliScore_abs_mean_le 3 p ![a, b, c] hp0 hp1
  norm_num only [Fin.prod_univ_two, Fin.prod_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Nat.reducePow, Nat.cast_ofNat] at h2 h3 h4 h5
  have htri (w : ι → Bool) : |bernoulliThirdScore p a b c ab ac bc abc w| ≤
      |bernoulliScoreSum p abc w| + |orderedBernoulliScore 2 p ![ab, c] w| +
      |orderedBernoulliScore 2 p ![ac, b] w| + |orderedBernoulliScore 2 p ![bc, a] w| +
      |orderedBernoulliScore 3 p ![a, b, c] w| := by
    rw [bernoulliThirdScore_decomposition]
    exact (abs_add _ _).trans (add_le_add_right ((abs_add _ _).trans
      (add_le_add_right ((abs_add _ _).trans (add_le_add_right (abs_add _ _) _)) _)) _)
  have hh := pmfMean_mono P htri
  simp only [pmfMean_add] at hh
  exact hh.trans (add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5)

end
end SampleReuse
