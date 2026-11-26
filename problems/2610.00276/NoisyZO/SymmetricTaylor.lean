import NoisyZO.VectorTaylor
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Symmetric averaging of vector Taylor terms

Central symmetry kills odd homogeneous terms in the vector Taylor expansion.
This file proves that fact directly for Bochner integrals and also records the
probability-average bound for the Hölder remainder.
-/

open MeasureTheory
open scoped BigOperators

namespace NoisyZO

noncomputable section

/-- A measure is centrally symmetric when negation preserves it. -/
def IsCentrallySymmetric
    {E : Type*} [MeasurableSpace E] [Neg E] (μ : Measure E) : Prop :=
  Measure.map (fun x : E ↦ -x) μ = μ

/-- The integral of an odd Banach-valued function under a centrally symmetric
measure is zero. -/
theorem integral_odd_eq_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) (hμ : IsCentrallySymmetric μ)
    (f : E → F) (hodd : ∀ x, f (-x) = -f x) :
    (∫ x, f x ∂μ) = 0 := by
  have hpres : MeasurePreserving (fun x : E ↦ -x) μ μ :=
    ⟨measurable_neg, hμ⟩
  have hinvariant : (∫ x, f (-x) ∂μ) = ∫ x, f x ∂μ :=
    hpres.integral_comp measurableEmbedding_neg f
  have hneg : (∫ x, f (-x) ∂μ) = -(∫ x, f x ∂μ) := by
    calc
      (∫ x, f (-x) ∂μ) = ∫ x, -f x ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hodd
      _ = -(∫ x, f x ∂μ) := by rw [integral_neg]
  have hself : -(∫ x, f x ∂μ) = ∫ x, f x ∂μ := hneg.symm.trans hinvariant
  have hdouble : (∫ x, f x ∂μ) + ∫ x, f x ∂μ = 0 := by
    exact neg_eq_iff_add_eq_zero.mp hself
  have htwo : (2 : ℝ) • (∫ x, f x ∂μ) = 0 := by
    simpa [two_smul ℝ] using hdouble
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- A multilinear form evaluated on a repeated scaled vector is homogeneous
of the degree given by its number of arguments. -/
theorem multilinear_diagonal_smul
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ E) F)
    (r : ℝ) (x : E) :
    A (fun _ ↦ r • x) = r ^ m • A (fun _ ↦ x) := by
  rw [A.map_smul_univ]
  simp

/-- An odd-degree multilinear diagonal is an odd function. -/
theorem multilinear_diagonal_neg_of_odd
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ E) F)
    (hm : Odd m) (x : E) :
    A (fun _ ↦ -x) = -A (fun _ ↦ x) := by
  calc
    A (fun _ ↦ -x) = (-1 : ℝ) ^ m • A (fun _ ↦ x) := by
      simpa only [neg_one_smul] using multilinear_diagonal_smul A (-1) x
    _ = -A (fun _ ↦ x) := by rw [hm.neg_one_pow, neg_one_smul]

/-- Every odd-degree Taylor coefficient vanishes after averaging against a
centrally symmetric measure. -/
theorem integral_multilinear_diagonal_eq_zero_of_odd
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) (hμ : IsCentrallySymmetric μ)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ E) F)
    (hm : Odd m) :
    (∫ x, A (fun _ ↦ x) ∂μ) = 0 := by
  exact integral_odd_eq_zero μ hμ (fun x ↦ A (fun _ ↦ x))
    (multilinear_diagonal_neg_of_odd A hm)

/-- Scaling the argument does not affect cancellation of odd Taylor terms. -/
theorem integral_scaled_multilinear_diagonal_eq_zero_of_odd
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) (hμ : IsCentrallySymmetric μ)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ E) F)
    (hm : Odd m) (r : ℝ) :
    (∫ x, A (fun _ ↦ r • x) ∂μ) = 0 := by
  have hfactor : (fun x ↦ A (fun _ ↦ r • x)) =
      fun x ↦ r ^ m • A (fun _ ↦ x) := by
    funext x
    exact multilinear_diagonal_smul A r x
  rw [hfactor, integral_smul]
  rw [integral_multilinear_diagonal_eq_zero_of_odd μ hμ A hm, smul_zero]

/-- Averaging the Hölder Taylor remainder over a probability measure supported
in the unit ball preserves its dimension-free operator-norm bound. -/
theorem norm_integral_holderTaylorRemainder_smul_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (g : E → F) (m : ℕ) (x : E) (r L α : ℝ)
    (hL : 0 ≤ L) (hα : 0 < α)
    (hunit : ∀ᵐ v ∂μ, ‖v‖ ≤ 1)
    (hholder : ∀ u v,
      ‖iteratedFDeriv ℝ m g u - iteratedFDeriv ℝ m g v‖ ≤
        L * ‖u - v‖ ^ α) :
    ‖∫ v, holderTaylorRemainder g m x (r • v) ∂μ‖ ≤
      (Nat.factorial (m - 1) : ℝ)⁻¹ *
        (L * |r| ^ α * |r| ^ m) := by
  have hae : ∀ᵐ v ∂μ,
      ‖holderTaylorRemainder g m x (r • v)‖ ≤
        (Nat.factorial (m - 1) : ℝ)⁻¹ *
          (L * |r| ^ α * |r| ^ m) := by
    filter_upwards [hunit] with v hv
    have hz : ‖r • v‖ ≤ |r| := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg r) hv
    have hzpow : ‖r • v‖ ^ m ≤ |r| ^ m := by
      exact (pow_le_pow_left₀ (norm_nonneg _) hz) m
    have hzrpow : ‖r • v‖ ^ α ≤ |r| ^ α :=
      Real.rpow_le_rpow (norm_nonneg _) hz (le_of_lt hα)
    refine (norm_holderTaylorRemainder_le g m x (r • v) L α hL hα hholder).trans ?_
    gcongr
  simpa using (norm_integral_le_of_norm_le_const hae)

/-- Probability averaging preserves the sharp `1/6` cubic remainder bound
for a Lipschitz second derivative. -/
theorem norm_integral_holderTaylorRemainder_two_smul_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (g : E → F) (x : E) (r : ℝ)
    (hunit : ∀ᵐ v ∂μ, ‖v‖ ≤ 1)
    (hholder : ∀ u v,
      ‖iteratedFDeriv ℝ 2 g u - iteratedFDeriv ℝ 2 g v‖ ≤ ‖u - v‖) :
    ‖∫ v, holderTaylorRemainder g 2 x (r • v) ∂μ‖ ≤ |r| ^ 3 / 6 := by
  have hae : ∀ᵐ v ∂μ,
      ‖holderTaylorRemainder g 2 x (r • v)‖ ≤ |r| ^ 3 / 6 := by
    filter_upwards [hunit] with v hv
    have hz : ‖r • v‖ ≤ |r| := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg r) hv
    calc
      ‖holderTaylorRemainder g 2 x (r • v)‖ ≤ ‖r • v‖ ^ 3 / 6 :=
        norm_holderTaylorRemainder_two_le g x (r • v) hholder
      _ ≤ |r| ^ 3 / 6 := by gcongr
  simpa using (norm_integral_le_of_norm_le_const hae)

end

end NoisyZO
