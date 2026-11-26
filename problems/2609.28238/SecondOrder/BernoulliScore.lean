import SecondOrder.BinaryRelativeEntropy
import SecondOrder.FiniteIndependentMoments
import SecondOrder.FiniteCauchySchwarz

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

/-- Logarithmic derivative of a Bernoulli mass at an interior parameter. -/
def binaryScore (p : ℝ) (b : Bool) : ℝ := if b then 1/p else -(1/(1-p))

theorem binaryScore_mean {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    pmfMean (binaryPMF p hp0.le hp1.le) (binaryScore p) = 0 := by
  simp only [pmfMean, smul_eq_mul, Fintype.sum_bool, binaryPMF_true_toReal,
    binaryPMF_false_toReal, binaryScore, Bool.false_eq_true, if_false, if_true]
  field_simp [hp0.ne', (sub_pos.mpr hp1).ne']

theorem binaryScore_second_moment {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    pmfMean (binaryPMF p hp0.le hp1.le) (fun b => binaryScore p b ^ 2) =
      1/(p*(1-p)) := by
  simp only [pmfMean, smul_eq_mul, Fintype.sum_bool, binaryPMF_true_toReal,
    binaryPMF_false_toReal, binaryScore, Bool.false_eq_true, if_false, if_true]
  field_simp [hp0.ne', (sub_pos.mpr hp1).ne']
  ring

theorem binaryScore_abs_mean {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    pmfMean (binaryPMF p hp0.le hp1.le) (fun b => |binaryScore p b|) = 2 := by
  simp only [pmfMean, smul_eq_mul, Fintype.sum_bool, binaryPMF_true_toReal,
    binaryPMF_false_toReal, binaryScore, Bool.false_eq_true, if_false, if_true,
    abs_neg, abs_of_pos (one_div_pos.mpr hp0),
    abs_of_pos (one_div_pos.mpr (sub_pos.mpr hp1))]
  field_simp [hp0.ne', (sub_pos.mpr hp1).ne']
  ring

variable {ι : Type*} [Fintype ι]

def bernoulliProduct (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    PMF (ι → Bool) := finitePiPMF (fun i => binaryPMF (p i) (hp0 i) (hp1 i))

def bernoulliScoreSum (p a : ι → ℝ) (w : ι → Bool) : ℝ :=
  ∑ i, a i * binaryScore (p i) (w i)

def bernoulliFisherEnergy (p a : ι → ℝ) : ℝ := ∑ i, a i^2/(p i*(1-p i))

theorem bernoulliScoreSum_mean (p a : ι → ℝ) (hp0 : ∀ i, 0 < p i)
    (hp1 : ∀ i, p i < 1) :
    pmfMean (bernoulliProduct p (fun i => (hp0 i).le) (fun i => (hp1 i).le))
      (bernoulliScoreSum p a) = 0 := by
  unfold bernoulliScoreSum bernoulliProduct
  rw [pmfMean_finset_sum]
  simp only [finitePiPMF_coordinate_mean, pmfMean_mul, binaryScore_mean (hp0 _) (hp1 _),
    mul_zero, Finset.sum_const_zero]

theorem bernoulliScoreSum_second_moment (p a : ι → ℝ) (hp0 : ∀ i, 0 < p i)
    (hp1 : ∀ i, p i < 1) :
    pmfMean (bernoulliProduct p (fun i => (hp0 i).le) (fun i => (hp1 i).le))
      (fun w => bernoulliScoreSum p a w ^ 2) = bernoulliFisherEnergy p a := by
  unfold bernoulliScoreSum bernoulliProduct bernoulliFisherEnergy
  rw [finitePiPMF_centered_square_sum _ (fun i b => a i * binaryScore (p i) b)]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [mul_pow, pmfMean_mul, binaryScore_second_moment (hp0 i) (hp1 i)]
    ring
  · intro i
    rw [pmfMean_mul, binaryScore_mean (hp0 i) (hp1 i), mul_zero]

theorem bernoulliScoreSum_abs_mean_le (p a : ι → ℝ) (hp0 : ∀ i, 0 < p i)
    (hp1 : ∀ i, p i < 1) :
    pmfMean (bernoulliProduct p (fun i => (hp0 i).le) (fun i => (hp1 i).le))
      (fun w => |bernoulliScoreSum p a w|) ≤ Real.sqrt (bernoulliFisherEnergy p a) := by
  simpa only [bernoulliScoreSum_second_moment p a hp0 hp1] using
    pmfMean_abs_le_sqrt (bernoulliProduct p (fun i => (hp0 i).le) (fun i => (hp1 i).le))
      (bernoulliScoreSum p a)

end
end SecondOrder
