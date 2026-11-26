import Matvec.CountLower
import Matvec.GaussianDiagonalLower
import LowRank.GaussianRightInverseMoment
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace Matvec
open MeasureTheory Matrix
open scoped Matrix BigOperators
noncomputable section

theorem square_inverse_trace_lower (n : ℕ) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    smallBallDensity * u / 4 ≤
      (LowRank.iidMatrixLaw (n + 1) (n + 1) 1).real
        {G | smallBallDensity * (n + 1 : ℝ) / (4 * u) ≤ (LowRank.inverseGram G).trace} := by
  let μ := LowRank.iidMatrixLaw (n + 1) (n + 1) 1
  letI : IsProbabilityMeasure μ := LowRank.iidMatrixLaw_probability _ _ _
  have hm (i : Fin (n + 1)) : Measurable
      (fun G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => LowRank.inverseGram G i i) :=
    (measurable_pi_apply i).comp ((measurable_pi_apply i).comp
      (LowRank.measurable_inverseGram (n + 1) (n + 1)))
  have h := sum_lower_probability_of_marginals μ
    (fun i G => LowRank.inverseGram G i i) hm (fun i G => LowRank.inverseGram_diagonal_nonneg G i)
    ((u ^ 2)⁻¹) (smallBallDensity * u / 2) (by positivity)
    (by have := smallBallDensity_pos; positivity)
    (fun i => square_inverse_diagonal_lower n i hu hu1)
  have heq : ((n + 1 : ℕ) : ℝ) * (smallBallDensity * u / 2) * (u ^ 2)⁻¹ / 2 =
      smallBallDensity * (n + 1 : ℝ) / (4 * u) := by
    push_cast
    field_simp [hu.ne']
    ring
  simpa only [Fintype.card_fin, heq, div_div, show (2 : ℝ) * 2 = 4 by norm_num,
    Matrix.trace, Matrix.diag, μ] using h

theorem rectangular_inverse_trace_tail {d k : ℕ} (hk : k + 2 ≤ d)
    {R : ℝ} (hR : 0 < R) :
    (LowRank.iidMatrixLaw d k 1).real {X | R < (LowRank.inverseGram X).trace} ≤
      ((k : ℝ) / ((d : ℝ) - k - 1)) / R := by
  have hm : Measurable (fun X : Matrix (Fin d) (Fin k) ℝ =>
      ENNReal.ofReal (LowRank.inverseGram X).trace) := by
    apply Measurable.ennreal_ofReal
    exact Finset.measurable_sum _ (fun i _ =>
      (measurable_pi_apply i).comp ((measurable_pi_apply i).comp
        (LowRank.measurable_inverseGram d k)))
  have h := meas_ge_le_lintegral_div (μ := LowRank.iidMatrixLaw d k 1)
    hm.aemeasurable (ε := ENNReal.ofReal R) (by positivity) ENNReal.ofReal_ne_top
  rw [LowRank.iidMatrixLaw_inverseGram_trace_mean hk,
    ← ENNReal.ofReal_div_of_pos hR] at h
  have hsub : {X : Matrix (Fin d) (Fin k) ℝ | R < (LowRank.inverseGram X).trace} ⊆
      {X | ENNReal.ofReal R ≤ ENNReal.ofReal (LowRank.inverseGram X).trace} :=
    fun X hX => ENNReal.ofReal_le_ofReal hX.le
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono hsub).trans h)
  have hden : 0 < (d : ℝ) - k - 1 := by
    have : (k : ℝ) + 2 ≤ d := by exact_mod_cast hk
    linarith
  simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity :
    0 ≤ ((k : ℝ) / ((d : ℝ) - k - 1)) / R)] using hr

theorem compressed_inverse_trace_tail {d k : ℕ}
    (B : Matrix (Fin d) (Fin k) ℝ) (hB : Bᵀ * B = 1) (hk : k + 2 ≤ d)
    {R : ℝ} (hR : 0 < R) :
    (LowRank.iidMatrixLaw d d 1).real {G | R < (LowRank.inverseGram (G * B)).trace} ≤
      ((k : ℝ) / ((d : ℝ) - k - 1)) / R := by
  have hmap := LowRank.iidMatrixLaw_right_compression (r := d) B hB 1
  have hm : MeasurableSet {X : Matrix (Fin d) (Fin k) ℝ |
      R < (LowRank.inverseGram X).trace} := by
    apply measurableSet_lt measurable_const
    exact Finset.measurable_sum _ (fun i _ =>
      (measurable_pi_apply i).comp ((measurable_pi_apply i).comp
        (LowRank.measurable_inverseGram d k)))
  have h := congrArg (fun μ : Measure (Matrix (Fin d) (Fin k) ℝ) =>
    μ {X | R < (LowRank.inverseGram X).trace}) hmap
  dsimp only at h
  have hmul : Measurable (fun G : Matrix (Fin d) (Fin d) ℝ => G * B) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    change Measurable (fun G : Matrix (Fin d) (Fin d) ℝ => ∑ l, G i l * B l j)
    apply Finset.measurable_sum
    intro l _
    apply Measurable.mul_const
    exact (measurable_pi_apply l).comp (measurable_pi_apply i)
  rw [Measure.map_apply hmul hm] at h
  have heq := congrArg ENNReal.toReal h
  exact heq.trans_le (rectangular_inverse_trace_tail hk hR)

end
end Matvec
