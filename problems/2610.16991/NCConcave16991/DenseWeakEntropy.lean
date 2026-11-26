import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

/-!
# Binary-entropy curvature for the row-information bound

This file proves the analytic Jensen-gap estimate used for one cell in Lemma
`lem:self-info`.  On the interval `[7/16, 9/16]`, binary entropy has curvature at most
`256/63`; convexity after adding the matching quadratic then gives the sharp factor `128/63`.
-/

namespace NCConcave16991.DenseWeakHiding

noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  Real.negMulLog p + Real.negMulLog (1 - p)

noncomputable def binaryEntropyD1 (p : ℝ) : ℝ :=
  Real.log (1 - p) - Real.log p

noncomputable def binaryEntropyD2 (p : ℝ) : ℝ :=
  -(1 - p)⁻¹ - p⁻¹

theorem hasDerivAt_binaryEntropy {p : ℝ} (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    HasDerivAt binaryEntropy (binaryEntropyD1 p) p := by
  have hleft := Real.hasDerivAt_negMulLog hp0
  have hsub : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) p :=
    by simpa only [id_eq] using (hasDerivAt_id p).const_sub (1 : ℝ)
  have hright := (Real.hasDerivAt_negMulLog (sub_ne_zero.mpr hp1.symm)).comp p hsub
  convert hleft.add hright using 1
  · funext x
    simp [binaryEntropy, Function.comp_def]
  · dsimp [binaryEntropyD1]
    ring

theorem hasDerivAt_binaryEntropyD1 {p : ℝ} (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    HasDerivAt binaryEntropyD1 (binaryEntropyD2 p) p := by
  have hsub : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) p :=
    by simpa only [id_eq] using (hasDerivAt_id p).const_sub (1 : ℝ)
  have hleft := (Real.hasDerivAt_log (sub_ne_zero.mpr hp1.symm)).comp p hsub
  have hright := Real.hasDerivAt_log hp0
  convert hleft.sub hright using 1
  · funext x
    simp [binaryEntropyD1, Function.comp_def]
  · dsimp [binaryEntropyD2]
    ring

noncomputable def entropyConvexEnvelope (p : ℝ) : ℝ :=
  (128 / 63 : ℝ) * p ^ 2 + binaryEntropy p

noncomputable def entropyConvexEnvelopeD1 (p : ℝ) : ℝ :=
  (256 / 63 : ℝ) * p + binaryEntropyD1 p

noncomputable def entropyConvexEnvelopeD2 (p : ℝ) : ℝ :=
  (256 / 63 : ℝ) + binaryEntropyD2 p

theorem hasDerivAt_entropyConvexEnvelope {p : ℝ} (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    HasDerivAt entropyConvexEnvelope (entropyConvexEnvelopeD1 p) p := by
  have hquad := ((hasDerivAt_pow 2 p).const_mul (128 / 63 : ℝ))
  convert hquad.add (hasDerivAt_binaryEntropy hp0 hp1) using 1
  · funext x
    simp [entropyConvexEnvelope]
  · simp [entropyConvexEnvelopeD1]
    ring

theorem hasDerivAt_entropyConvexEnvelopeD1 {p : ℝ} (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    HasDerivAt entropyConvexEnvelopeD1 (entropyConvexEnvelopeD2 p) p := by
  have hlin := (hasDerivAt_id p).const_mul (256 / 63 : ℝ)
  convert hlin.add (hasDerivAt_binaryEntropyD1 hp0 hp1) using 1
  · funext x
    simp [entropyConvexEnvelopeD1]
  · simp [entropyConvexEnvelopeD2]

/-- On the central interval, `p(1-p)` is bounded below by `63/256`. -/
theorem bernoulliVariance_lower {p : ℝ}
    (hp : p ∈ Set.Icc (7 / 16 : ℝ) (9 / 16 : ℝ)) :
    63 / 256 ≤ p * (1 - p) := by
  rcases hp with ⟨hp0, hp1⟩
  nlinarith [sq_nonneg (p - 1 / 2)]

theorem entropyConvexEnvelopeD2_nonneg {p : ℝ}
    (hp : p ∈ Set.Icc (7 / 16 : ℝ) (9 / 16 : ℝ)) :
    0 ≤ entropyConvexEnvelopeD2 p := by
  rcases hp with ⟨hp0, hp1⟩
  have hp_pos : 0 < p := by linarith
  have h1p_pos : 0 < 1 - p := by linarith
  have hprod_pos : 0 < p * (1 - p) := mul_pos hp_pos h1p_pos
  have hprod := bernoulliVariance_lower ⟨hp0, hp1⟩
  have hinv : 1 / (p * (1 - p)) ≤ (256 / 63 : ℝ) := by
    apply (div_le_iff₀ hprod_pos).2
    nlinarith
  have hsum : (1 - p)⁻¹ + p⁻¹ = 1 / (p * (1 - p)) := by
    field_simp [hp_pos.ne', h1p_pos.ne']
    ring
  rw [entropyConvexEnvelopeD2, binaryEntropyD2]
  rw [← hsum] at hinv
  linarith

theorem entropyConvexEnvelope_convexOn :
    ConvexOn ℝ (Set.Icc (7 / 16 : ℝ) (9 / 16 : ℝ)) entropyConvexEnvelope := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
  · exact ((continuous_const.mul (continuous_pow 2)).add
      (Real.continuous_negMulLog.add
        (Real.continuous_negMulLog.comp (continuous_const.sub continuous_id')))).continuousOn
  · intro p hp
    rw [interior_Icc] at hp
    exact (hasDerivAt_entropyConvexEnvelope (by linarith [hp.1])
      (by linarith [hp.2])).hasDerivWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    exact (hasDerivAt_entropyConvexEnvelopeD1 (by linarith [hp.1])
      (by linarith [hp.2])).hasDerivWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    exact entropyConvexEnvelopeD2_nonneg ⟨hp.1.le, hp.2.le⟩

/-- The binary-entropy Jensen gap for a two-point Bernoulli channel. -/
theorem binaryEntropy_jensenGap_le
    {pi p q : ℝ}
    (hpi0 : 0 ≤ pi) (hpi1 : pi ≤ 1)
    (hp : p ∈ Set.Icc (7 / 16 : ℝ) (9 / 16 : ℝ))
    (hq : q ∈ Set.Icc (7 / 16 : ℝ) (9 / 16 : ℝ)) :
    binaryEntropy (pi * p + (1 - pi) * q) -
        (pi * binaryEntropy p + (1 - pi) * binaryEntropy q) ≤
      (128 / 63 : ℝ) * pi * (1 - pi) * (p - q) ^ 2 := by
  have hj := entropyConvexEnvelope_convexOn.2 hp hq hpi0 (sub_nonneg.mpr hpi1)
    (by ring : pi + (1 - pi) = 1)
  simp only [smul_eq_mul] at hj
  dsimp [entropyConvexEnvelope] at hj
  nlinarith [sq_nonneg (p - q)]

end NCConcave16991.DenseWeakHiding

/- Adapted from the local 0105_formalization/Manuscript0105/BinaryEntropy.lean. These analytic lemmas are reused for the cited dense weak hiding dependency; they do not assert its oracle lower bound. -/
