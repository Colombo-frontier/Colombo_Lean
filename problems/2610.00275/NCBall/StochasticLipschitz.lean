import NCBall.ClassParameters
import NCBall.GaussianMaximum
import NCBall.NoiseEmbedding

/-! # A sample Lipschitz modulus with the required second moment

The noise scale is σ = L₀ / γ. The proof uses the actual product Gaussian
sample space and the maximum-moment estimate, not an assumed second moment.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace NCBall

def sampleLipschitzModulus {n M : ℕ} (γ L : ℝ) (z : Fin M → Fin n → ℝ) : ℝ :=
  γ * (bumpConstant + 2) + (L / 16) * Real.sqrt (maximumNormSq z)

theorem sampleLipschitzModulus_nonneg {n M : ℕ} {γ L : ℝ}
    (hγ : 0 ≤ γ) (hL : 0 ≤ L) (z : Fin M → Fin n → ℝ) :
    0 ≤ sampleLipschitzModulus γ L z := by
  have := bumpConstant_pos
  unfold sampleLipschitzModulus
  positivity

theorem roomNoise_le_maximum {n M : ℕ} (z : Fin M → Fin n → ℝ) {j : ℕ} (hj : j < M) :
    ‖roomNoise z j‖ ≤ Real.sqrt (maximumNormSq z) := by
  have hb := le_nonnegativeMaximum Finset.univ (fun i => coordinateNormSq (z i))
    (Finset.mem_univ (⟨j, hj⟩ : Fin M))
  change coordinateNormSq (z ⟨j, hj⟩) ≤ maximumNormSq z at hb
  have he := roomNoise_norm_sq z hj
  have hs := Real.sq_sqrt (nonnegativeMaximum_nonneg Finset.univ (fun i => coordinateNormSq (z i)))
  change Real.sqrt (maximumNormSq z) ^ 2 = maximumNormSq z at hs
  have hp := Real.sqrt_nonneg (maximumNormSq z)
  nlinarith [norm_nonneg (roomNoise z j)]

theorem gaussian_sample_lipschitz {n M : ℕ} {ρ γ L : ℝ}
    (hρ : 0 < ρ) (hγ : 0 < γ) (hL : 0 ≤ L) (U : ℕ → Space n)
    (hU : ∀ i, U i 0 = 0) (hgood : ∀ i < M, ‖U i‖ ≤ 2)
    (z : Fin M → Fin n → ℝ) :
    LipschitzWith ⟨sampleLipschitzModulus γ L z, sampleLipschitzModulus_nonneg hγ.le hL z⟩
      (chainValue M ρ γ (calibratedLam γ) (roomCenter ρ U)
        (fun j => U j + (L / γ) • roomNoise z j)) := by
  have hC := bumpConstant_pos
  have hB : 0 ≤ 2 + (L / γ) * Real.sqrt (maximumNormSq z) := by positivity
  have hV : ∀ j < M, ‖U j + (L / γ) • roomNoise z j‖ ≤
      2 + (L / γ) * Real.sqrt (maximumNormSq z) := by
    intro j hj
    calc
      _ ≤ ‖U j‖ + ‖(L / γ) • roomNoise z j‖ := norm_add_le _ _
      _ = ‖U j‖ + (L / γ) * ‖roomNoise z j‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ _ := add_le_add (hgood j hj)
        (mul_le_mul_of_nonneg_left (roomNoise_le_maximum z hj) (by positivity))
  have hlip := chainValue_lipschitz hρ hγ.le (calibratedLam_bounds hγ.le).1 hB
    U (fun j => U j + (L / γ) • roomNoise z j) hU hV
  have hbound : γ + calibratedLam γ * bumpConstant *
      (2 + (L / γ) * Real.sqrt (maximumNormSq z)) + γ * bumpConstant ≤ sampleLipschitzModulus γ L z := by
    have heq : calibratedLam γ * bumpConstant *
        (2 + (L / γ) * Real.sqrt (maximumNormSq z)) =
        γ / 8 + (L / 16) * Real.sqrt (maximumNormSq z) := by
      unfold calibratedLam
      field_simp
      ring
    rw [heq]
    unfold sampleLipschitzModulus
    nlinarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (hlip.dist_le_mul x y).trans (mul_le_mul_of_nonneg_right hbound dist_nonneg)

theorem sampleLipschitzModulus_square_bound {n M : ℕ} (γ L : ℝ) (z : Fin M → Fin n → ℝ) :
    sampleLipschitzModulus γ L z ^ 2 ≤
      2 * (γ * (bumpConstant + 2)) ^ 2 + (L ^ 2 / 128) * maximumNormSq z := by
  have hs := Real.sq_sqrt (nonnegativeMaximum_nonneg Finset.univ (fun i => coordinateNormSq (z i)))
  change Real.sqrt (maximumNormSq z) ^ 2 = maximumNormSq z at hs
  have hd := sq_nonneg (γ * (bumpConstant + 2) - (L / 16) * Real.sqrt (maximumNormSq z))
  unfold sampleLipschitzModulus
  nlinarith [congrArg (fun r => L ^ 2 * r) hs]

theorem sampleLipschitzModulus_square_integrable {n M : ℕ} (hn : 0 < n) (γ L : ℝ) :
    Integrable (fun z => sampleLipschitzModulus γ L z ^ 2) (gaussianRooms n M) := by
  have hc : Continuous (fun z : Fin M → Fin n → ℝ => sampleLipschitzModulus γ L z ^ 2) := by
    unfold sampleLipschitzModulus
    exact (continuous_const.add (continuous_const.mul
      ((maximumNormSq_continuous n M).sqrt))).pow 2
  have hi : Integrable (fun z : Fin M → Fin n → ℝ =>
      2 * (γ * (bumpConstant + 2)) ^ 2 + (L ^ 2 / 128) * maximumNormSq z) (gaussianRooms n M) :=
    (integrable_const _).add ((gaussianRooms_maximum_integrable hn).const_mul _)
  apply hi.mono' hc.aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sampleLipschitzModulus_square_bound γ L z

/-- Equation (7.8) with fully specified constants and an actual sample modulus. -/
theorem gaussian_sample_lipschitz_second_moment {n M : ℕ} (hn : 0 < n)
    (hsize : (M : ℝ) * Real.exp (-(n : ℝ) / 2) ≤ 1)
    {γ L : ℝ} (hγ : 0 ≤ γ)
    (hscale : γ * (bumpConstant + 2) ≤ L / 4) :
    (∫ z, sampleLipschitzModulus γ L z ^ 2 ∂gaussianRooms n M) ≤ L ^ 2 := by
  have hC := bumpConstant_pos
  have hm := gaussianRooms_maximum_expectation hn hsize
  have hi := sampleLipschitzModulus_square_integrable (M := M) hn γ L
  have he : Integrable (fun z : Fin M → Fin n → ℝ =>
      2 * (γ * (bumpConstant + 2)) ^ 2 + (L ^ 2 / 128) * maximumNormSq z) (gaussianRooms n M) :=
    (integrable_const _).add ((gaussianRooms_maximum_integrable hn).const_mul _)
  have hb := integral_mono hi he (sampleLipschitzModulus_square_bound γ L)
  rw [integral_add (integrable_const _) ((gaussianRooms_maximum_integrable hn).const_mul _),
    integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul, integral_const_mul] at hb
  have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ L ^ 2 / 128)
  have hs := mul_self_le_mul_self (by positivity : 0 ≤ γ * (bumpConstant + 2)) hscale
  nlinarith [sq_nonneg L]

end NCBall
