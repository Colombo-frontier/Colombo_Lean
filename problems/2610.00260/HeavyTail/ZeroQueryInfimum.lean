import HeavyTail.ZeroQuery
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! Exact optimization of the zero-query bound in the reciprocal proximal
step. The zero reciprocal endpoint represents the infimum over arbitrarily
large finite steps; the finite factor-two realization is proved in ZeroQuery. -/
noncomputable section
namespace HeavyTail

def reciprocalZeroQueryBound (μ D G z : ℝ) : ℝ := D ^ 2 * z / 2 + G ^ 2 / (2 * (μ + z))

theorem reciprocalZeroQueryBound_identity {μ D G z r : ℝ} (hden : μ + z ≠ 0) :
    reciprocalZeroQueryBound μ D G z - radialObjective μ G r =
      z / 2 * (D ^ 2 - r ^ 2) + (G - (μ + z) * r) ^ 2 / (2 * (μ + z)) := by
  unfold reciprocalZeroQueryBound radialObjective
  field_simp
  <;> ring

theorem reciprocalZeroQueryBound_ge_envelope {μ D G z : ℝ}
    (hμ : 0 ≤ μ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hz : 0 ≤ z) (hden : 0 < μ + z) :
    envelope μ D G ≤ reciprocalZeroQueryBound μ D G z := by
  have hr0 := envelopeRadius_nonneg hμ hD hG
  have hrD : envelopeRadius μ D G ≤ D := envelopeRadius_le
  have hs : (envelopeRadius μ D G) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hr0 hrD 2
  have he := reciprocalZeroQueryBound_identity (D := D) (G := G)
    (r := envelopeRadius μ D G) hden.ne'
  change envelope μ D G ≤ _
  have hn : 0 ≤ z / 2 * (D ^ 2 - (envelopeRadius μ D G) ^ 2) +
      (G - (μ + z) * envelopeRadius μ D G) ^ 2 / (2 * (μ + z)) :=
    add_nonneg (mul_nonneg (div_nonneg hz (by norm_num)) (sub_nonneg.mpr hs))
      (div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) hden.le))
  change reciprocalZeroQueryBound μ D G z - envelope μ D G = _ at he
  linarith only [he, hn]

def optimalReciprocalStep (μ D G : ℝ) : ℝ := max 0 (G / D - μ)

theorem optimalReciprocalStep_nonneg (μ D G : ℝ) : 0 ≤ optimalReciprocalStep μ D G :=
  le_max_left _ _

theorem reciprocalZeroQueryBound_at_optimum {μ D G : ℝ}
    (hμ : 0 < μ) (hD : 0 < D) (hG : 0 ≤ G) :
    reciprocalZeroQueryBound μ D G (optimalReciprocalStep μ D G) = envelope μ D G := by
  by_cases hb : G ≤ μ * D
  · have hz : G / D - μ ≤ 0 := by
      have hh := (div_le_iff₀ hD).mpr hb
      linarith
    rw [optimalReciprocalStep, max_eq_left hz, envelope_quadratic hμ hb]
    simp only [reciprocalZeroQueryBound, mul_zero, zero_div, add_zero, zero_add]
  · have hb' : μ * D ≤ G := (le_of_not_ge hb)
    have hz : 0 ≤ G / D - μ := by
      have hh := (le_div_iff₀ hD).mpr hb'
      linarith
    have hGp : 0 < G := (mul_pos hμ hD).trans_le hb'
    rw [optimalReciprocalStep, max_eq_right hz, envelope_linear hμ hb']
    unfold reciprocalZeroQueryBound
    have hd : μ + (G / D - μ) = G / D := by ring
    rw [hd]
    field_simp
    <;> ring

/-- The exact reciprocal-step optimization stated after eq:zero. -/
theorem zero_query_reciprocal_infimum {μ D G : ℝ}
    (hμ : 0 < μ) (hD : 0 < D) (hG : 0 ≤ G) :
    sInf {b : ℝ | ∃ z : ℝ, 0 ≤ z ∧ b = reciprocalZeroQueryBound μ D G z} =
      envelope μ D G := by
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨optimalReciprocalStep μ D G, optimalReciprocalStep_nonneg μ D G,
      (reciprocalZeroQueryBound_at_optimum hμ hD hG).symm⟩
  · rintro b ⟨z, hz, rfl⟩
    exact reciprocalZeroQueryBound_ge_envelope hμ.le hD.le hG hz (by positivity)

end HeavyTail
