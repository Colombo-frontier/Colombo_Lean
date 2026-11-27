import Nonsmooth.GaussianSquareMGF
import Nonsmooth.GaussianConcentration

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem euclideanGaussian_square_exponential_integral {t : ℝ} (ht : t < 1 / 2) :
    (∫ z : E, Real.exp (t * ‖z‖ ^ 2) ∂euclideanGaussianLaw E) =
      ((Real.sqrt (1 - 2 * t))⁻¹) ^ Module.finrank ℝ E := by
  have h := euclideanGaussian_norm_square_identDistrib (E := E)
  have hcomp := h.comp ((measurable_const.mul measurable_id).exp : Measurable (fun z : ℝ => Real.exp (t * z)))
  exact hcomp.integral_eq.symm.trans (standardGaussianCoordinates_square_exponential _ ht)

theorem euclideanGaussian_square_exponential_integrable {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun z : E => Real.exp (t * ‖z‖ ^ 2)) (euclideanGaussianLaw E) := by
  by_contra h
  have hi := euclideanGaussian_square_exponential_integral (E := E) ht
  rw [integral_undef h] at hi
  have hp : 0 < ((Real.sqrt (1 - 2 * t))⁻¹) ^ Module.finrank ℝ E :=
    pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))) _
  linarith

theorem euclideanGaussian_square_exponential_formula {t : ℝ} (ht : t < 1 / 2) :
    (∫ z : E, Real.exp (t * ‖z‖ ^ 2) ∂euclideanGaussianLaw E) =
      Real.exp (-((Module.finrank ℝ E : ℝ) / 2) * Real.log (1 - 2 * t)) := by
  rw [euclideanGaussian_square_exponential_integral ht]
  have hc : 0 < 1 - 2 * t := by linarith
  have hp : 0 < (Real.sqrt (1 - 2 * t))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hc)
  calc
    _ = Real.exp ((Module.finrank ℝ E : ℝ) * Real.log ((Real.sqrt (1 - 2 * t))⁻¹)) := by
      rw [Real.exp_nat_mul, Real.exp_log hp]
    _ = _ := by
      rw [Real.log_inv, Real.log_sqrt hc.le]
      congr 1
      ring

theorem euclideanGaussian_square_chernoff (t b : ℝ) (ht : t < 1 / 2) :
    (euclideanGaussianLaw E).real {z : E | b ≤ t * ‖z‖ ^ 2} ≤
      Real.exp (-b - ((Module.finrank ℝ E : ℝ) / 2) * Real.log (1 - 2 * t)) := by
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := euclideanGaussianLaw E)
    (f := fun z : E => Real.exp (t * ‖z‖ ^ 2)) (Eventually.of_forall (fun z => (Real.exp_pos _).le))
    (euclideanGaussian_square_exponential_integrable ht) (Real.exp b)
  rw [euclideanGaussian_square_exponential_formula ht] at hm
  have he : {z : E | Real.exp b ≤ Real.exp (t * ‖z‖ ^ 2)} = {z : E | b ≤ t * ‖z‖ ^ 2} := by
    ext z; simp only [Set.mem_setOf_eq, Real.exp_le_exp]
  rw [he] at hm
  have h : (euclideanGaussianLaw E).real {z : E | b ≤ t * ‖z‖ ^ 2} ≤
      Real.exp (-((Module.finrank ℝ E : ℝ) / 2) * Real.log (1 - 2 * t)) / Real.exp b :=
    (le_div_iff₀ (Real.exp_pos b)).mpr (by simpa only [mul_comm (Real.exp b)] using hm)
  calc
    _ ≤ Real.exp (-((Module.finrank ℝ E : ℝ) / 2) * Real.log (1 - 2 * t)) / Real.exp b := h
    _ = _ := by
      rw [← Real.exp_sub]
      congr 1
      ring

theorem euclideanGaussian_square_upper_exponential :
    (euclideanGaussianLaw E).real {z : E | 2 * (Module.finrank ℝ E : ℝ) ≤ ‖z‖ ^ 2} ≤
      Real.exp (-(Module.finrank ℝ E : ℝ) / 32) := by
  let d := Module.finrank ℝ E
  have h := euclideanGaussian_square_chernoff (E := E) (1 / 8) ((d : ℝ) / 4) (by norm_num)
  have he : {z : E | (d : ℝ) / 4 ≤ 1 / 8 * ‖z‖ ^ 2} = {z : E | 2 * (d : ℝ) ≤ ‖z‖ ^ 2} := by
    ext z
    simp only [Set.mem_setOf_eq]
    constructor <;> intro hz <;> linarith
  rw [he] at h
  norm_num only [show (1 : ℝ) - 2 * (1 / 8) = 3 / 4 from by norm_num] at h
  have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 4)
  norm_num at hl
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (d : ℝ) / 2)
  exact h.trans (Real.exp_le_exp.mpr (by change -((d : ℝ) / 4) - (d : ℝ) / 2 * Real.log (3 / 4) ≤ -(d : ℝ) / 32; nlinarith))

theorem euclideanGaussian_square_lower_exponential :
    (euclideanGaussianLaw E).real {z : E | ‖z‖ ^ 2 ≤ (Module.finrank ℝ E : ℝ) / 2} ≤
      Real.exp (-(Module.finrank ℝ E : ℝ) / 32) := by
  let d := Module.finrank ℝ E
  have h := euclideanGaussian_square_chernoff (E := E) (-1 / 8) (-(d : ℝ) / 16) (by norm_num)
  have he : {z : E | -(d : ℝ) / 16 ≤ (-1 / 8) * ‖z‖ ^ 2} = {z : E | ‖z‖ ^ 2 ≤ (d : ℝ) / 2} := by
    ext z
    simp only [Set.mem_setOf_eq]
    constructor <;> intro hz <;> linarith
  rw [he] at h
  norm_num only [show (1 : ℝ) - 2 * (-1 / 8) = 5 / 4 from by norm_num] at h
  have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 5 / 4)
  norm_num at hl
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (d : ℝ) / 2)
  exact h.trans (Real.exp_le_exp.mpr (by change -(-(d : ℝ) / 16) - (d : ℝ) / 2 * Real.log (5 / 4) ≤ -(d : ℝ) / 32; nlinarith))

theorem euclideanGaussian_square_two_sided_exponential :
    (euclideanGaussianLaw E).real {z : E |
      ‖z‖ ^ 2 < (Module.finrank ℝ E : ℝ) / 2 ∨ 2 * (Module.finrank ℝ E : ℝ) < ‖z‖ ^ 2} ≤
        2 * Real.exp (-(Module.finrank ℝ E : ℝ) / 32) := by
  have hs : {z : E | ‖z‖ ^ 2 < (Module.finrank ℝ E : ℝ) / 2 ∨ 2 * (Module.finrank ℝ E : ℝ) < ‖z‖ ^ 2} ⊆
      {z : E | ‖z‖ ^ 2 ≤ (Module.finrank ℝ E : ℝ) / 2} ∪ {z : E | 2 * (Module.finrank ℝ E : ℝ) ≤ ‖z‖ ^ 2} := by
    intro z hz
    exact hz.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le)
  have h := (measureReal_mono (μ := euclideanGaussianLaw E) hs (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  have hl := euclideanGaussian_square_lower_exponential (E := E)
  have hu := euclideanGaussian_square_upper_exponential (E := E)
  linarith

end
end Nonsmooth
