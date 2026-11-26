import GradientHessian.MatrixGoodAnalytic
import Mathlib.Probability.ConditionalProbability

/-! The manuscript's actual conditioned Gaussian source and preservation of
independent external randomness when only the matrix event is conditioned. -/

namespace GradientHessian.ConditionedSource
open MeasureTheory ProbabilityTheory Matrix LowRank MatrixKernelConcentration
open scoped ENNReal
noncomputable section

def sourceLaw {d n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (J : ℕ) :
    Measure (Matrix (Fin d) (Fin n) ℝ) :=
  cond (gaussianMatrixLaw d n) (sourceGoodEvent P J)

theorem sourceLaw_probability {J r κ k D : ℕ}
    (hJ : 4 ≤ J) (hr : 1 + 4096 * J ^ 2 ≤ r) (hκ : 18874368 ≤ κ)
    (hk : k = κ * r) (hD : D = k * J)
    (P : Matrix (Fin D) (Fin D) ℝ) (hP : IsOrthogonalProjector P) (hrank : P.rank = r) :
    IsProbabilityMeasure (sourceLaw (n := D-k) P J) := by
  apply cond_isProbabilityMeasure
  intro hz
  have hp := manuscript_sourceGoodEvent_probability hJ hr hκ hk hD P hP hrank
  rw [measureReal_def, hz, ENNReal.toReal_zero] at hp
  norm_num at hp

theorem sourceLaw_good {d n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (J : ℕ) :
    ∀ᵐ X ∂sourceLaw (n := n) P J, X ∈ sourceGoodEvent P J :=
  ae_cond_mem (measurableSet_sourceGoodEvent P J)

theorem sourceLaw_analytic {d n : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) {J : ℕ} (hJ : 4 ≤ J) :
    ∀ᵐ X ∂sourceLaw (n := n) P J, MatrixGoodAnalytic.GoodAnalytic P J X := by
  filter_upwards [sourceLaw_good (n := n) P J] with X hX
  exact MatrixGoodAnalytic.sourceGoodEvent_analytic hP hJ hX

theorem cond_real_apply {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {E : Set Ω} (hE : MeasurableSet E) (S : Set Ω) :
    (cond μ E).real S = μ.real (E ∩ S) / μ.real E := by
  simp only [measureReal_def, cond_apply hE, ENNReal.toReal_mul, ENNReal.toReal_inv]
  ring

theorem cond_real_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {E : Set Ω} (hE : MeasurableSet E) (S : Set Ω) :
    (cond μ E).real S ≤ μ.real S / μ.real E := by
  rw [cond_real_apply μ hE]
  exact div_le_div_of_nonneg_right (measureReal_mono Set.inter_subset_right) (measureReal_nonneg)

/-- Conditioning only the first coordinate preserves the entire original
second-coordinate law. It may include seeds, earlier independent marks and
any independent external data. -/
theorem condition_matrix_only {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure T) [IsProbabilityMeasure ν]
    {E : Set Ω} (hE : MeasurableSet E) :
    cond (μ.prod ν) (E ×ˢ Set.univ) = (cond μ E).prod ν := by
  symm
  apply Measure.prod_eq
  intro S U hS hU
  rw [cond_apply (hE.prod MeasurableSet.univ), cond_apply hE,
    Set.prod_inter_prod, Set.univ_inter, Measure.prod_prod, Measure.prod_prod,
    measure_univ, mul_one, mul_assoc]

end
end GradientHessian.ConditionedSource
