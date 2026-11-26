import SecondOrder.BernoulliScore

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem bernoulliFisherEnergy_nonneg (p a : ι → ℝ) (hp0 : ∀ i, 0 < p i)
    (hp1 : ∀ i, p i < 1) : 0 ≤ bernoulliFisherEnergy p a := by
  exact Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (mul_pos (hp0 i) (sub_pos.mpr (hp1 i))).le)

/-- Cauchy–Schwarz in the diagonal Bernoulli Fisher metric. -/
theorem bernoulliFisher_cross_le (p a b : ι → ℝ) (hp0 : ∀ i, 0 < p i)
    (hp1 : ∀ i, p i < 1) :
    (∑ i, |a i*b i|/(p i*(1-p i))) ≤
      Real.sqrt (bernoulliFisherEnergy p a)*Real.sqrt (bernoulliFisherEnergy p b) := by
  have hv (i : ι) : 0 ≤ p i*(1-p i) := (mul_pos (hp0 i) (sub_pos.mpr (hp1 i))).le
  have hs (x : ι → ℝ) (i : ι) :
      (|x i|/Real.sqrt (p i*(1-p i)))^2 = x i^2/(p i*(1-p i)) := by
    rw [div_pow, sq_abs, Real.sq_sqrt (hv i)]
  have hm (i : ι) :
      (|a i|/Real.sqrt (p i*(1-p i)))*(|b i|/Real.sqrt (p i*(1-p i))) =
        |a i*b i|/(p i*(1-p i)) := by
    rw [div_mul_div_comm, ← abs_mul, Real.mul_self_sqrt (hv i)]
  have hh := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i => |a i|/Real.sqrt (p i*(1-p i)))
    (fun i => |b i|/Real.sqrt (p i*(1-p i)))
  simpa only [hm, hs, bernoulliFisherEnergy] using hh

theorem bernoulliScoreSum_abs_mean_le_sum (p c : ι → ℝ) (hp0 : ∀ i, 0 < p i)
    (hp1 : ∀ i, p i < 1) :
    pmfMean (bernoulliProduct p (fun i => (hp0 i).le) (fun i => (hp1 i).le))
      (fun w => |bernoulliScoreSum p c w|) ≤ 2 * ∑ i, |c i| := by
  calc
    _ ≤ pmfMean (bernoulliProduct p (fun i => (hp0 i).le) (fun i => (hp1 i).le))
        (fun w => ∑ i, |c i*binaryScore (p i) (w i)|) :=
      pmfMean_mono _ (fun w => Finset.abs_sum_le_sum_abs _ _)
    _ = _ := by
      rw [pmfMean_finset_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [bernoulliProduct, abs_mul, pmfMean_mul]
      rw [finitePiPMF_coordinate_mean _ i (fun b => |binaryScore (p i) b|),
        binaryScore_abs_mean (hp0 i) (hp1 i)]
      ring

def bernoulliScoreDiagonal (p a b : ι → ℝ) (w : ι → Bool) : ℝ :=
  ∑ i, (a i*b i)*binaryScore (p i) (w i)^2

theorem bernoulliScoreDiagonal_abs_mean_le (p a b : ι → ℝ) (hp0 : ∀ i, 0 < p i)
    (hp1 : ∀ i, p i < 1) :
    pmfMean (bernoulliProduct p (fun i => (hp0 i).le) (fun i => (hp1 i).le))
      (fun w => |bernoulliScoreDiagonal p a b w|) ≤
        Real.sqrt (bernoulliFisherEnergy p a)*Real.sqrt (bernoulliFisherEnergy p b) := by
  calc
    _ ≤ pmfMean (bernoulliProduct p (fun i => (hp0 i).le) (fun i => (hp1 i).le))
        (fun w => ∑ i, |(a i*b i)*binaryScore (p i) (w i)^2|) :=
      pmfMean_mono _ (fun w => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ i, |a i*b i|/(p i*(1-p i)) := by
      rw [pmfMean_finset_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [bernoulliProduct, abs_mul, abs_pow, sq_abs, pmfMean_mul]
      rw [finitePiPMF_coordinate_mean _ i (fun b => binaryScore (p i) b ^ 2),
        binaryScore_second_moment (hp0 i) (hp1 i)]
      ring
    _ ≤ _ := bernoulliFisher_cross_le p a b hp0 hp1

/-- Normalized mixed second derivative of the product mass; the diagonal
correction removes the repeated differentiation of one Bernoulli factor. -/
def bernoulliSecondScore (p a b c : ι → ℝ) (w : ι → Bool) : ℝ :=
  bernoulliScoreSum p c w + bernoulliScoreSum p a w * bernoulliScoreSum p b w -
    bernoulliScoreDiagonal p a b w

theorem bernoulliSecondScore_abs_mean_le (p a b c : ι → ℝ)
    (hp0 : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) :
    pmfMean (bernoulliProduct p (fun i => (hp0 i).le) (fun i => (hp1 i).le))
      (fun w => |bernoulliSecondScore p a b c w|) ≤
        2 * ∑ i, |c i| +
          2 * Real.sqrt (bernoulliFisherEnergy p a)*Real.sqrt (bernoulliFisherEnergy p b) := by
  let P := bernoulliProduct p (fun i => (hp0 i).le) (fun i => (hp1 i).le)
  have hcross : pmfMean P (fun w => |bernoulliScoreSum p a w * bernoulliScoreSum p b w|) ≤
      Real.sqrt (bernoulliFisherEnergy p a)*Real.sqrt (bernoulliFisherEnergy p b) := by
    simpa only [P, bernoulliScoreSum_second_moment p a hp0 hp1,
      bernoulliScoreSum_second_moment p b hp0 hp1] using
      pmfMean_abs_mul_le P (bernoulliScoreSum p a) (bernoulliScoreSum p b)
  have htri (w : ι → Bool) : |bernoulliSecondScore p a b c w| ≤
      |bernoulliScoreSum p c w| + |bernoulliScoreSum p a w * bernoulliScoreSum p b w| +
        |bernoulliScoreDiagonal p a b w| := by
    exact (abs_sub _ _).trans (add_le_add_right (abs_add _ _) _)
  have hh := pmfMean_mono P htri
  rw [pmfMean_add, pmfMean_add] at hh
  have hfirst := bernoulliScoreSum_abs_mean_le_sum p c hp0 hp1
  have hdiag := bernoulliScoreDiagonal_abs_mean_le p a b hp0 hp1
  change pmfMean P _ ≤ _ at hfirst hdiag ⊢
  linarith

end
end SecondOrder
