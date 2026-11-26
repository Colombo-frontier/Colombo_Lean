import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Scalar binary Pinsker inequality

This file isolates the one-dimensional analytic inequality underlying the event form of
Pinsker's inequality.  The convention is the natural-log convention, so the sharp quadratic
constant below is `2`.
-/

namespace NoisyZO

open Set

/-- Relative entropy of a Bernoulli parameter `p` from a reference parameter `q`, written in a
form that is continuous at `p = 0, 1`. -/
noncomputable def binaryRelativeEntropy (p q : ℝ) : ℝ :=
  -Real.binEntropy p - p * Real.log q - (1 - p) * Real.log (1 - q)

private noncomputable def binaryPinskerAux (q p : ℝ) : ℝ :=
  binaryRelativeEntropy p q - 2 * (p - q) ^ 2

private noncomputable def binaryPinskerSlope (q p : ℝ) : ℝ :=
  -(Real.log (1 - p) - Real.log p) - Real.log q + Real.log (1 - q) - 4 * (p - q)

private noncomputable def binaryPinskerCurvature (p : ℝ) : ℝ :=
  1 / (p * (1 - p)) - 4

private theorem hasDerivAt_binaryPinskerAux {p q : ℝ} (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    HasDerivAt (binaryPinskerAux q) (binaryPinskerSlope q p) p := by
  have hId : HasDerivAt (fun x : ℝ ↦ x) 1 p := by
    change HasDerivAt id 1 p
    exact hasDerivAt_id p
  have hOneSub : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) p := by
    convert (hasDerivAt_const p (1 : ℝ)).sub hId using 1 <;> norm_num
  have hLinear₁ : HasDerivAt (fun x : ℝ ↦ x * Real.log q) (Real.log q) p := by
    convert hId.mul_const (Real.log q) using 1 <;> ring
  have hLinear₂ :
      HasDerivAt (fun x : ℝ ↦ (1 - x) * Real.log (1 - q)) (-Real.log (1 - q)) p := by
    convert hOneSub.mul_const (Real.log (1 - q)) using 1 <;> ring
  have hDiff : HasDerivAt (fun x : ℝ ↦ x - q) 1 p := by
    convert hId.sub (hasDerivAt_const p q) using 1 <;> norm_num
  have hQuadratic : HasDerivAt (fun x : ℝ ↦ 2 * (x - q) ^ 2) (4 * (p - q)) p := by
    convert (hDiff.pow 2).const_mul 2 using 1 <;> ring
  convert (((Real.hasDerivAt_binEntropy hp0 hp1).neg.sub hLinear₁).sub hLinear₂).sub
    hQuadratic using 1
  · funext x
    simp only [binaryPinskerAux, binaryRelativeEntropy, Pi.sub_apply, Pi.neg_apply]
  · simp only [binaryPinskerSlope]
    ring_nf

private theorem hasDerivAt_binaryPinskerSlope {p q : ℝ} (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    HasDerivAt (binaryPinskerSlope q) (binaryPinskerCurvature p) p := by
  have hId : HasDerivAt (fun x : ℝ ↦ x) 1 p := by
    change HasDerivAt id 1 p
    exact hasDerivAt_id p
  have hOneSub : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) p := by
    convert (hasDerivAt_const p (1 : ℝ)).sub hId using 1 <;> norm_num
  have hLogOneSub : HasDerivAt (fun x : ℝ ↦ Real.log (1 - x)) (-1 / (1 - p)) p := by
    convert hOneSub.log (sub_ne_zero.mpr hp1.symm) using 1 <;> ring
  have hLog : HasDerivAt (fun x : ℝ ↦ Real.log x) (1 / p) p := by
    convert hId.log hp0 using 1 <;> ring
  have hLogDiff :
      HasDerivAt (fun x : ℝ ↦ -(Real.log (1 - x) - Real.log x))
        (1 / (1 - p) + 1 / p) p := by
    convert (hLogOneSub.sub hLog).neg using 1 <;> ring
  have hDiff : HasDerivAt (fun x : ℝ ↦ x - q) 1 p := by
    convert hId.sub (hasDerivAt_const p q) using 1 <;> norm_num
  have hLast : HasDerivAt (fun x : ℝ ↦ 4 * (x - q)) 4 p := by
    convert hDiff.const_mul 4 using 1 <;> ring
  have hConstants :
      HasDerivAt (fun _ : ℝ ↦ Real.log q - Real.log (1 - q)) 0 p :=
    hasDerivAt_const p _
  have h := (hLogDiff.sub hConstants).sub hLast
  convert h using 1
  · funext x
    simp only [binaryPinskerSlope, Pi.sub_apply, Pi.neg_apply]
    ring_nf
  · simp only [binaryPinskerCurvature]
    field_simp [hp0, sub_ne_zero.mpr hp1.symm]
    <;> ring

private theorem binaryPinskerCurvature_nonneg {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 ≤ binaryPinskerCurvature p := by
  have hprod : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp1)
  simp only [binaryPinskerCurvature, sub_nonneg]
  rw [le_div_iff₀ hprod]
  nlinarith [sq_nonneg (2 * p - 1)]

private theorem binaryPinskerAux_convex (q : ℝ) :
    ConvexOn ℝ (Icc 0 1) (binaryPinskerAux q) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
  · apply Continuous.continuousOn
    unfold binaryPinskerAux binaryRelativeEntropy
    fun_prop
  · intro p hp
    simp only [interior_Icc, mem_Ioo] at hp
    exact (hasDerivAt_binaryPinskerAux hp.1.ne' hp.2.ne).hasDerivWithinAt
  · intro p hp
    simp only [interior_Icc, mem_Ioo] at hp
    exact (hasDerivAt_binaryPinskerSlope hp.1.ne' hp.2.ne).hasDerivWithinAt
  · intro p hp
    simp only [interior_Icc, mem_Ioo] at hp
    exact binaryPinskerCurvature_nonneg hp.1 hp.2

private theorem binaryPinskerAux_self {q : ℝ} : binaryPinskerAux q q = 0 := by
  simp only [binaryPinskerAux, binaryRelativeEntropy, Real.binEntropy]
  rw [Real.log_inv, Real.log_inv]
  ring

/-- Scalar binary Pinsker inequality (natural logarithms): for Bernoulli parameters `p, q`,
`2 (p - q)² ≤ D(p ∥ q)`.  The reference parameter is kept in the open interval so the displayed
cross-entropy expression is finite. -/
theorem two_sq_sub_le_binaryRelativeEntropy {p q : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hq0 : 0 < q) (hq1 : q < 1) :
    2 * (p - q) ^ 2 ≤ binaryRelativeEntropy p q := by
  have hqInterior : q ∈ interior (Icc (0 : ℝ) 1) := by
    simpa only [interior_Icc, mem_Ioo] using And.intro hq0 hq1
  have hq0' : q ≠ 0 := hq0.ne'
  have hq1' : q ≠ 1 := hq1.ne
  have hderiv : derivWithin (binaryPinskerAux q) (Ioi q) q = 0 := by
    apply (hasDerivAt_binaryPinskerAux hq0' hq1').hasDerivWithinAt.derivWithin
      (uniqueDiffWithinAt_Ioi q) |>.trans
    simp only [binaryPinskerSlope]
    ring
  have hmin := (binaryPinskerAux_convex q).isMinOn_of_rightDeriv_eq_zero hqInterior hderiv
  have hle : binaryPinskerAux q q ≤ binaryPinskerAux q p := hmin hp
  rw [binaryPinskerAux_self] at hle
  change 0 ≤ binaryRelativeEntropy p q - 2 * (p - q) ^ 2 at hle
  linarith

end NoisyZO
