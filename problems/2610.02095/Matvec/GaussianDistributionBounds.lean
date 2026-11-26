import Matvec.GaussianLowEvent
import Matvec.SquareGaussianUpper

/-! Actual dimension-uniform low and high events for square Gaussian least
stretch. These bounds are weaker than the cited sharp hard edge, but suffice
for the manuscript's separated-events argument and reliable source promise. -/
namespace Matvec
open MeasureTheory Matrix LowRank
open scoped Matrix
noncomputable section

theorem gaussian_leastStretch_low (n : ℕ) (hn : lowEventRank ≤ n)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    smallBallDensity ^ 2 * a ^ 2 / (64 * lowEventRank) ≤
      (iidMatrixLaw (n + 1) (n + 1) 1).real
        {G | leastStretch (matrixEuclideanMap G) ≤ a / Real.sqrt (n + 1 : ℝ)} := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hl := square_inverse_top_at_scale m ha ha1
  let μ := iidMatrixLaw (lowEventRank + m + 1) (lowEventRank + m + 1) 1
  letI : IsProbabilityMeasure μ := iidMatrixLaw_probability _ _ _
  apply hl.trans
  apply ENNReal.toReal_mono (measure_ne_top μ _)
  apply measure_mono_ae
  filter_upwards [iidMatrixLaw_mulVec_injective_ae (lowEventRank + m + 1)
    (lowEventRank + m + 1) le_rfl (by norm_num : (1 : NNReal) ≠ 0)] with G hG
  intro hlarge
  have h := leastStretch_le_of_inverseGram_eigenvalue G (by omega) hG
    (Fin.last (lowEventRank + m)) ((lowEventRank + (m + 1) : ℝ) / a ^ 2)
    (by positivity) hlarge
  have hs : (Real.sqrt ((lowEventRank + (m + 1) : ℝ) / a ^ 2))⁻¹ =
      a / Real.sqrt (lowEventRank + m + 1 : ℝ) := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq ha.le, inv_div]
    congr 2 <;> ring
  simpa only [Nat.cast_add, Nat.cast_one] using h.trans_eq hs

theorem gaussian_leastStretch_high (n : ℕ) {R : ℝ} (hR : 0 < R) :
    1 - squareInverseTailConstant / R ^ (1 / 4 : ℝ) ≤
      (iidMatrixLaw (n + 1) (n + 1) 1).real
        {G | (Real.sqrt (R * (n + 1 : ℝ)))⁻¹ ≤ leastStretch (matrixEuclideanMap G)} := by
  let μ := iidMatrixLaw (n + 1) (n + 1) 1
  letI : IsProbabilityMeasure μ := iidMatrixLaw_probability _ _ _
  let E := {G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ |
    (Real.sqrt (R * (n + 1 : ℝ)))⁻¹ ≤ leastStretch (matrixEuclideanMap G)}
  let F := {G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ |
    R * (n + 1 : ℝ) < inverseGramEigenvalue G (Fin.last n)}
  have hall : ∀ᵐ G ∂μ, G ∈ E ∪ F := by
    filter_upwards [iidMatrixLaw_mulVec_injective_ae (n + 1) (n + 1) le_rfl
      (by norm_num : (1 : NNReal) ≠ 0)] with G hG
    by_cases hf : G ∈ F
    · exact Or.inr hf
    · left
      have hbound : inverseGramEigenvalue G (Fin.last n) ≤ R * (n + 1 : ℝ) :=
        le_of_not_gt hf
      apply matrix_leastStretch_lower G (by omega)
      exact (inverseGram_top_expansion G hG (R * (n + 1 : ℝ))
        ((Real.sqrt (R * (n + 1 : ℝ)))⁻¹) (by positivity) (by positivity)
        (by rw [inv_pow, Real.sq_sqrt (by positivity)]) hbound).2
  have hm : 1 ≤ μ.real E + μ.real F := by
    have hsub : ∀ᵐ G ∂μ, G ∈ (Set.univ : Set
        (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) → G ∈ E ∪ F :=
      hall.mono (fun _ h _ => h)
    have h := (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)).trans
      (measureReal_union_le E F)
    change μ.real Set.univ ≤ _ at h
    simpa only [measureReal_univ_eq_one] using h
  have ht := square_inverse_eigenvalue_tail n (Fin.last n) R hR
  change _ ≤ μ.real E
  change μ.real F ≤ _ at ht
  linarith

/-- The high event can have arbitrarily high fixed reliability, uniformly in
dimension, with a correspondingly small positive scale. -/
theorem gaussian_reliable_high_scale (δ : ℝ) (hδ : 0 < δ) :
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 ∧ ∀ n : ℕ,
      1 - δ ≤ (iidMatrixLaw (n + 1) (n + 1) 1).real
        {G | b / Real.sqrt (n + 1 : ℝ) ≤ leastStretch (matrixEuclideanMap G)} := by
  let B := squareInverseTailConstant / δ + 1
  have hC := squareInverseTailConstant_pos
  have hB : 1 < B := by dsimp [B]; linarith [div_pos hC hδ]
  have hB0 : 0 < B := by linarith
  refine ⟨(B ^ 2)⁻¹, by positivity, ?_, ?_⟩
  · apply (inv_le_one₀ (by positivity : 0 < B ^ 2)).mpr
    nlinarith
  · intro n
    have h := gaussian_leastStretch_high n (R := B ^ 4) (by positivity)
    have hpow : (B ^ 4) ^ (1 / 4 : ℝ) = B := by
      rw [← Real.rpow_natCast_mul hB0.le]
      norm_num
    have hsqrt : Real.sqrt (B ^ 4) = B ^ 2 := by
      rw [show B ^ 4 = (B ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg B)]
    have heq : (Real.sqrt (B ^ 4 * (n + 1 : ℝ)))⁻¹ =
        (B ^ 2)⁻¹ / Real.sqrt (n + 1 : ℝ) := by
      rw [Real.sqrt_mul (by positivity), hsqrt, mul_inv]
      rfl
    rw [hpow, heq] at h
    apply le_trans _ h
    have hratio : squareInverseTailConstant / B ≤ δ := by
      apply (div_le_iff₀ hB0).mpr
      dsimp [B]
      nlinarith [div_mul_cancel₀ squareInverseTailConstant hδ.ne']
    linarith

/-- Separated unconditional Gaussian events with universal positive constants.
The low event also applies to any independent fresh square core. -/
theorem gaussian_separated_constants :
    ∃ a b p : ℝ, 0 < a ∧ a ≤ 1 ∧ 0 < b ∧ 0 < p ∧ 4 * a < b ∧
      (∀ n : ℕ, lowEventRank ≤ n →
        p ≤ (iidMatrixLaw (n + 1) (n + 1) 1).real
          {G | leastStretch (matrixEuclideanMap G) ≤ a / Real.sqrt (n + 1 : ℝ)}) ∧
      (∀ n : ℕ, (1 / 2 : ℝ) ≤ (iidMatrixLaw (n + 1) (n + 1) 1).real
          {G | b / Real.sqrt (n + 1 : ℝ) ≤ leastStretch (matrixEuclideanMap G)}) := by
  obtain ⟨b, hb, hb1, hhigh⟩ := gaussian_reliable_high_scale (1 / 2) (by norm_num)
  let a := b / 8
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have hr : (0 : ℝ) < lowEventRank := by exact_mod_cast (by
    have := lowEventRank_ge_two; omega : 0 < lowEventRank)
  refine ⟨a, b, smallBallDensity ^ 2 * a ^ 2 / (64 * lowEventRank), ha, ha1,
    hb, ?_, ?_, ?_, ?_⟩
  · have := smallBallDensity_pos; positivity
  · dsimp [a]; linarith
  · intro n hn
    exact gaussian_leastStretch_low n hn ha ha1
  · intro n
    have h := hhigh n
    norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h
    exact h

end
end Matvec
