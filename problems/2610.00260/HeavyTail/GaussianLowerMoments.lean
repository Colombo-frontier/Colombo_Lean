import HeavyTail.GaussianDirections
import HeavyTail.HardFamily
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Genuine Gaussian trace-oracle moment admissibility

The Gaussian law is the concrete finite-dimensional law already constructed
in GaussianDirections. This file proves its vector mean, trace, and all real
moments of order at most two, then instantiates the actual hard-family oracle.
It does not postulate an adaptive testing or likelihood-ratio bound.
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace BigOperators

namespace HeavyTail
noncomputable section

lemma gaussianLower_abs_rpow_le_square (x : ℝ) {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) :
    |x| ^ p ≤ 1 + x ^ 2 := by
  by_cases hx : |x| ≤ 1
  · exact (Real.rpow_le_one (abs_nonneg x) hx hp).trans (by nlinarith [sq_nonneg x])
  · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx) hp2
    rw [Real.rpow_two, sq_abs] at h
    linarith

lemma gaussianLower_square_rpow (x p : ℝ) : (x ^ 2) ^ (p / 2) = |x| ^ p := by
  rw [← sq_abs x, ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg x)]
  congr 1
  ring

theorem probability_moment_le_second {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {p : ℝ}
    (hX : Measurable X) (h2 : Integrable (fun ω ↦ X ω ^ 2) P)
    (hp : 0 ≤ p) (hp2 : p ≤ 2) :
    (∫ ω, |X ω| ^ p ∂P) ≤ (∫ ω, X ω ^ 2 ∂P) ^ (p / 2) := by
  have hi : Integrable (fun ω ↦ |X ω| ^ p) P := by
    apply ((integrable_const (1 : ℝ)).add h2).mono'
    · exact (Real.continuous_rpow_const hp).comp_aestronglyMeasurable hX.abs.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact gaussianLower_abs_rpow_le_square _ hp hp2
  have hip : Integrable ((fun x : ℝ ↦ x ^ (p / 2)) ∘ fun ω ↦ X ω ^ 2) P := by
    simpa only [Function.comp_def, gaussianLower_square_rpow] using hi
  have hj := (Real.concaveOn_rpow (by linarith : 0 ≤ p / 2) (by linarith : p / 2 ≤ 1)).le_map_integral
    (Real.continuous_rpow_const (by linarith : 0 ≤ p / 2)).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall fun ω ↦ sq_nonneg (X ω)) h2 hip
  simpa only [gaussianLower_square_rpow] using hj

theorem probability_moment_le_of_second_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {p K : ℝ}
    (hX : Measurable X) (h2 : Integrable (fun ω ↦ X ω ^ 2) P)
    (hp : 0 ≤ p) (hp2 : p ≤ 2) (hK : 0 ≤ K)
    (hbound : (∫ ω, X ω ^ 2 ∂P) ≤ K ^ 2) :
    (∫ ω, |X ω| ^ p ∂P) ≤ K ^ p := by
  calc
    _ ≤ (∫ ω, X ω ^ 2 ∂P) ^ (p / 2) := probability_moment_le_second hX h2 hp hp2
    _ ≤ (K ^ 2) ^ (p / 2) := Real.rpow_le_rpow
      (integral_nonneg fun ω ↦ sq_nonneg _) hbound (by linarith)
    _ = K ^ p := by rw [gaussianLower_square_rpow, abs_of_nonneg hK]

namespace GaussianLower
open GaussianEstimates

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem norm_square_representation (z : E) :
    ‖z‖ ^ 2 = ∑ i, ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using
    ((stdOrthonormalBasis ℝ E).sum_sq_norm_inner z).symm

theorem gaussian_norm_square_integrable :
    Integrable (fun z : E ↦ ‖z‖ ^ 2) (euclideanGaussianLaw E) := by
  simp_rw [norm_square_representation E]
  exact integrable_finset_sum _ fun i _ ↦ gaussian_inner_power_integrable E _ 2

theorem gaussian_norm_square_integral :
    (∫ z : E, ‖z‖ ^ 2 ∂euclideanGaussianLaw E) = (Module.finrank ℝ E : ℝ) := by
  simp_rw [norm_square_representation E]
  rw [integral_finset_sum _ (fun i _ ↦ gaussian_inner_power_integrable E _ 2)]
  simp_rw [gaussian_inner_second]
  simp [(stdOrthonormalBasis ℝ E).orthonormal.norm_eq_one]

theorem gaussian_id_integrable : Integrable (fun z : E ↦ z) (euclideanGaussianLaw E) := by
  have hcoord (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun z : E ↦ ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ) (euclideanGaussianLaw E) := by
    simpa only [pow_one] using gaussian_inner_power_integrable E (stdOrthonormalBasis ℝ E i) 1
  have hi := integrable_finset_sum Finset.univ
    (fun i _ ↦ (hcoord i).smul_const (stdOrthonormalBasis ℝ E i))
  simpa only [(stdOrthonormalBasis ℝ E).sum_repr'] using hi

theorem gaussian_vector_mean_zero : (∫ z : E, z ∂euclideanGaussianLaw E) = 0 := by
  have hz : (fun z : E ↦ z) =
      fun z ↦ ∑ i, ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ • stdOrthonormalBasis ℝ E i := by
    funext z
    exact ((stdOrthonormalBasis ℝ E).sum_repr' z).symm
  rw [hz, integral_finset_sum _ (fun i _ ↦
    ((by simpa only [pow_one] using gaussian_inner_power_integrable E (stdOrthonormalBasis ℝ E i) 1)
      : Integrable (fun z ↦ ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ) (euclideanGaussianLaw E)).smul_const _)]
  simp_rw [integral_smul_const, gaussian_inner_mean_zero]
  simp

theorem scaled_gaussian_second_integrable (σ : ℝ) :
    Integrable (fun z : E ↦ ‖σ • z‖ ^ 2) (euclideanGaussianLaw E) := by
  simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using
    (gaussian_norm_square_integrable E).const_mul (σ ^ 2)

theorem scaled_gaussian_second (σ : ℝ) :
    (∫ z : E, ‖σ • z‖ ^ 2 ∂euclideanGaussianLaw E) = σ ^ 2 * Module.finrank ℝ E := by
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [integral_const_mul, gaussian_norm_square_integral]

theorem scaled_gaussian_direction_second_integrable (σ : ℝ) (v : E) :
    Integrable (fun z : E ↦ ⟪v, σ • z⟫_ℝ ^ 2) (euclideanGaussianLaw E) := by
  simpa only [inner_smul_right, mul_pow] using
    (gaussian_inner_power_integrable E v 2).const_mul (σ ^ 2)

theorem scaled_gaussian_direction_second (σ : ℝ) (v : E) :
    (∫ z : E, ⟪v, σ • z⟫_ℝ ^ 2 ∂euclideanGaussianLaw E) = σ ^ 2 * ‖v‖ ^ 2 := by
  simp only [inner_smul_right, mul_pow]
  rw [integral_const_mul, gaussian_inner_second]

theorem gaussian_two_moment_admissible {σ L s p : ℝ}
    (hL : 0 ≤ L) (hs : 0 ≤ s) (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (htrace : σ ^ 2 * Module.finrank ℝ E ≤ L ^ 2) (hdir : σ ^ 2 ≤ s ^ 2) :
    (∫ z : E, ‖σ • z‖ ^ p ∂euclideanGaussianLaw E) ≤ L ^ p ∧
    ∀ v : E, ‖v‖ = 1 →
      (∫ z : E, |⟪v, σ • z⟫_ℝ| ^ p ∂euclideanGaussianLaw E) ≤ s ^ p := by
  constructor
  · have h := probability_moment_le_of_second_bound
      (show Measurable (fun z : E ↦ ‖σ • z‖) by fun_prop)
      (scaled_gaussian_second_integrable E σ) hp hp2 hL
      (by rwa [scaled_gaussian_second])
    simpa only [abs_norm] using h
  · intro v hv
    apply probability_moment_le_of_second_bound
      (show Measurable (fun z : E ↦ ⟪v, σ • z⟫_ℝ) by fun_prop)
      (scaled_gaussian_direction_second_integrable E σ v) hp hp2 hs
    rw [scaled_gaussian_direction_second, hv]
    simpa using hdir

end GaussianLower

def gaussianTraceOracle {k : ℕ} (a ρ σ : ℝ) (v : Fin k → ℝ)
    (x z : HardSpace k) : HardSpace k := hardGradient a ρ v x + σ • z

theorem gaussianTraceOracle_unbiased {k : ℕ} (a ρ σ : ℝ) (v : Fin k → ℝ) (x : HardSpace k) :
    (∫ z, gaussianTraceOracle a ρ σ v x z ∂GaussianEstimates.euclideanGaussianLaw (HardSpace k)) =
      hardGradient a ρ v x := by
  unfold gaussianTraceOracle
  have hi : Integrable (fun z : HardSpace k ↦ σ • z)
      (GaussianEstimates.euclideanGaussianLaw (HardSpace k)) :=
    (GaussianLower.gaussian_id_integrable (HardSpace k)).smul σ
  rw [integral_add (integrable_const _) hi,
    integral_const, integral_smul, GaussianLower.gaussian_vector_mean_zero]
  simp

theorem gaussianTraceOracle_moment_admissible {k : ℕ} (hk : 0 < k)
    {L s p : ℝ} (hL : 0 ≤ L) (hs : 0 ≤ s) (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hdim : L ^ 2 ≤ (k : ℝ) * s ^ 2) (a ρ : ℝ) (v : Fin k → ℝ) (x : HardSpace k) :
    (∫ z, ‖gaussianTraceOracle a ρ (L / Real.sqrt k) v x z - hardGradient a ρ v x‖ ^ p
      ∂GaussianEstimates.euclideanGaussianLaw (HardSpace k)) ≤ L ^ p ∧
    ∀ w : HardSpace k, ‖w‖ = 1 →
      (∫ z, |⟪w, gaussianTraceOracle a ρ (L / Real.sqrt k) v x z - hardGradient a ρ v x⟫_ℝ| ^ p
        ∂GaussianEstimates.euclideanGaussianLaw (HardSpace k)) ≤ s ^ p := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hvar : (L / Real.sqrt (k : ℝ)) ^ 2 = L ^ 2 / k := by
    rw [div_pow, Real.sq_sqrt hkR.le]
  have htrace : (L / Real.sqrt (k : ℝ)) ^ 2 * Module.finrank ℝ (HardSpace k) ≤ L ^ 2 := by
    rw [hvar]
    simp only [HardSpace, finrank_euclideanSpace_fin]
    exact le_of_eq (div_mul_cancel₀ _ hkR.ne')
  have hdir : (L / Real.sqrt (k : ℝ)) ^ 2 ≤ s ^ 2 := by
    rw [hvar]
    exact (div_le_iff₀ hkR).mpr (by simpa only [mul_comm] using hdim)
  simpa only [gaussianTraceOracle, add_sub_cancel_left] using
    GaussianLower.gaussian_two_moment_admissible (HardSpace k) hL hs hp hp2 htrace hdir

end
end HeavyTail
