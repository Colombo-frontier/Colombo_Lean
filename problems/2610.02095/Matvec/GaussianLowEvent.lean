import Matvec.GaussianTraceLower
import Matvec.InverseTraceCompression
import Matvec.SpectralBridge
import Matvec.KernelFrame

/-! A positive small-singular-value event for square Gaussian matrices.
The proof uses inverse diagonal marginals, a fixed-codimension compression,
and the rectangular inverse-trace moment, rather than an external hard-edge
asymptotic. Every probability assertion is for the actual iid Gaussian law. -/
namespace Matvec
open Matrix MeasureTheory LowRank
open scoped Matrix BigOperators
noncomputable section

theorem square_inverse_trace_compression {r m : ℕ}
    (G : Matrix (Fin (r + (m + 1))) (Fin (r + (m + 1))) ℝ)
    (hG : Function.Injective G.mulVec)
    (B : Matrix (Fin (r + (m + 1))) (Fin (m + 1)) ℝ) (hB : Bᵀ * B = 1) :
    (inverseGram G).trace ≤
      r * inverseGramEigenvalue G (Fin.last (r + m)) + (inverseGram (G * B)).trace := by
  have hBinj : Function.Injective B.mulVec := by
    intro x y hxy
    have h := congrArg (fun v => Bᵀ *ᵥ v) hxy
    simpa only [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec] using h
  have hGBinj : Function.Injective (G * B).mulVec := by
    intro x y hxy
    apply hBinj
    apply hG
    simpa only [Matrix.mulVec_mulVec] using hxy
  let spA := orderedMatrixSpectrum (rightGram_posSemidef G).isHermitian
  let spC := orderedMatrixSpectrum (rightGram_posSemidef (G * B)).isHermitian
  exact inverse_trace_compression_le spA spC B hB
    (by simp only [Matrix.transpose_mul, Matrix.mul_assoc])
    (fun i => (ordered_gram_values_pos G hG spA i).ne')
    (ordered_gram_values_pos (G * B) hGBinj spC) _ (inverseGram_le_top G)

/-- Low-event estimate before choosing the absolute compression codimension. -/
theorem square_inverse_top_lower_raw {r m : ℕ} (hr : 2 ≤ r)
    (B : Matrix (Fin (r + (m + 1))) (Fin (m + 1)) ℝ) (hB : Bᵀ * B = 1)
    {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    smallBallDensity * u / 4 - 8 * u / (smallBallDensity * ((r : ℝ) - 1)) ≤
      (iidMatrixLaw (r + (m + 1)) (r + (m + 1)) 1).real
        {G | smallBallDensity * (r + (m + 1) : ℝ) / (8 * r * u) ≤
          inverseGramEigenvalue G (Fin.last (r + m))} := by
  let μ := iidMatrixLaw (r + (m + 1)) (r + (m + 1)) 1
  letI : IsProbabilityMeasure μ := iidMatrixLaw_probability _ _ _
  let T := smallBallDensity * (r + (m + 1) : ℝ) / (8 * u)
  let E := {G : Matrix (Fin (r + (m + 1))) (Fin (r + (m + 1))) ℝ |
    smallBallDensity * (r + (m + 1) : ℝ) / (8 * r * u) ≤
      inverseGramEigenvalue G (Fin.last (r + m))}
  let F := {G : Matrix (Fin (r + (m + 1))) (Fin (r + (m + 1))) ℝ |
    T < (inverseGram (G * B)).trace}
  have hc := smallBallDensity_pos
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hN : (0 : ℝ) < r + (m + 1) := by positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hlow := square_inverse_trace_lower (r + m) hu hu1
  have hsub : ∀ᵐ G ∂μ, G ∈ {G | smallBallDensity * (r + m + 1 : ℝ) / (4 * u) ≤
      (inverseGram G).trace} → G ∈ E ∪ F := by
    filter_upwards [iidMatrixLaw_mulVec_injective_ae (r + (m + 1))
      (r + (m + 1)) le_rfl (by norm_num : (1 : NNReal) ≠ 0)] with G hG
    intro htrace
    by_cases hF : G ∈ F
    · exact Or.inr hF
    · left
      have hrect : (inverseGram (G * B)).trace ≤ T := le_of_not_gt hF
      have hcomp := square_inverse_trace_compression G hG B hB
      change smallBallDensity * (r + (m + 1) : ℝ) / (8 * r * u) ≤ _
      apply (div_le_iff₀ (by positivity : 0 < (8 : ℝ) * r * u)).mpr
      have ht : smallBallDensity * (r + (m + 1) : ℝ) = T * (8 * u) := by
        dsimp [T]; field_simp [hu.ne']
      have hl : 2 * T ≤ (inverseGram G).trace := by
        dsimp [T]
        convert htrace using 1 <;> ring
      nlinarith
  have hm : μ.real {G | smallBallDensity * (r + m + 1 : ℝ) / (4 * u) ≤
      (inverseGram G).trace} ≤ μ.real E + μ.real F :=
    (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)).trans
      (measureReal_union_le E F)
  have htail := compressed_inverse_trace_tail B hB (by omega : m + 1 + 2 ≤ r + (m + 1)) hT
  have htail' : μ.real F ≤ 8 * u / (smallBallDensity * ((r : ℝ) - 1)) := by
    apply htail.trans
    have hden : (0 : ℝ) < r - 1 := by linarith
    have hN' : (m + 1 : ℝ) ≤ r + (m + 1) := by linarith
    dsimp [T]
    push_cast
    have heq : (r : ℝ) + ((m : ℝ) + 1) - ((m : ℝ) + 1) - 1 = r - 1 := by ring
    rw [heq]
    calc
      _ = ((m + 1 : ℝ) / (r + (m + 1))) *
          (8 * u / (smallBallDensity * ((r : ℝ) - 1))) := by
        field_simp [hc.ne', hden.ne', hN.ne', hu.ne']
        ring
      _ ≤ 1 * (8 * u / (smallBallDensity * ((r : ℝ) - 1))) :=
        mul_le_mul_of_nonneg_right ((div_le_one hN).mpr hN') (by positivity)
      _ = _ := one_mul _
  have hlow' : smallBallDensity * u / 4 ≤
      μ.real {G | smallBallDensity * (r + m + 1 : ℝ) / (4 * u) ≤ (inverseGram G).trace} := by
    simpa only [Nat.cast_add, Nat.cast_one] using hlow
  change _ ≤ μ.real E
  linarith

theorem smallBallDensity_le_two : smallBallDensity ≤ 2 := by
  have h := gaussian_small_interval_lower (u := 1) (by norm_num) le_rfl
  have hprob : (ProbabilityTheory.gaussianReal 0 1).real (Set.Icc (1 / 2) 1) ≤ 1 :=
    (measureReal_mono (Set.subset_univ _)).trans_eq measureReal_univ_eq_one
  nlinarith

/-- A universal fixed codimension; its numerical size affects only constants. -/
def lowEventRank : ℕ := ⌈64 / smallBallDensity ^ 2⌉₊ + 2

theorem lowEventRank_ge_two : 2 ≤ lowEventRank := by unfold lowEventRank; omega

theorem lowEventRank_large : 64 ≤ smallBallDensity ^ 2 * ((lowEventRank : ℝ) - 1) := by
  have hc := smallBallDensity_pos
  have h := Nat.le_ceil (64 / smallBallDensity ^ 2)
  have h' := (div_le_iff₀ (by positivity : 0 < smallBallDensity ^ 2)).mp h
  unfold lowEventRank
  push_cast
  nlinarith [sq_nonneg smallBallDensity]

/-- Uniform positive inverse-eigenvalue low event in every sufficiently large
dimension. The orthonormal compression is constructed, not assumed. -/
theorem square_inverse_top_lower (m : ℕ) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    smallBallDensity * u / 8 ≤
      (iidMatrixLaw (lowEventRank + (m + 1)) (lowEventRank + (m + 1)) 1).real
        {G | smallBallDensity * (lowEventRank + (m + 1) : ℝ) /
          (8 * lowEventRank * u) ≤ inverseGramEigenvalue G (Fin.last (lowEventRank + m))} := by
  let B := kernelFrame (0 : Matrix (Fin lowEventRank)
    (Fin (lowEventRank + (m + 1))) ℝ) (m + 1)
  have hB : Bᵀ * B = 1 := kernelFrame_orthonormal _ (by omega)
  have h := square_inverse_top_lower_raw lowEventRank_ge_two B hB hu hu1
  apply le_trans _ h
  have hc := smallBallDensity_pos
  have hr : (2 : ℝ) ≤ lowEventRank := by exact_mod_cast lowEventRank_ge_two
  have hden : 0 < smallBallDensity * ((lowEventRank : ℝ) - 1) :=
    mul_pos hc (by linarith)
  have htail : 8 * u / (smallBallDensity * ((lowEventRank : ℝ) - 1)) ≤
      smallBallDensity * u / 8 := by
    apply (div_le_iff₀ hden).mpr
    have hlarge := mul_le_mul_of_nonneg_right lowEventRank_large hu.le
    nlinarith
  linarith

/-- Reparametrization at the natural square-Gaussian scale N/a². -/
theorem square_inverse_top_at_scale (m : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    smallBallDensity ^ 2 * a ^ 2 / (64 * lowEventRank) ≤
      (iidMatrixLaw (lowEventRank + (m + 1)) (lowEventRank + (m + 1)) 1).real
        {G | (lowEventRank + (m + 1) : ℝ) / a ^ 2 ≤
          inverseGramEigenvalue G (Fin.last (lowEventRank + m))} := by
  have hc := smallBallDensity_pos
  have hr : (2 : ℝ) ≤ lowEventRank := by exact_mod_cast lowEventRank_ge_two
  have hu : 0 < smallBallDensity * a ^ 2 / (8 * lowEventRank) := by positivity
  have hu1 : smallBallDensity * a ^ 2 / (8 * lowEventRank) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * lowEventRank)).mpr
    have hc2 := smallBallDensity_le_two
    have ha2 : a ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left ha2 hc.le]
  have h := square_inverse_top_lower m hu hu1
  have heq : smallBallDensity * (lowEventRank + (m + 1) : ℝ) /
      (8 * lowEventRank * (smallBallDensity * a ^ 2 / (8 * lowEventRank))) =
      (lowEventRank + (m + 1) : ℝ) / a ^ 2 := by
    field_simp
    ring
  have heq' : smallBallDensity * (smallBallDensity * a ^ 2 / (8 * lowEventRank)) / 8 =
      smallBallDensity ^ 2 * a ^ 2 / (64 * lowEventRank) := by ring
  rwa [heq, heq'] at h

end
end Matvec
