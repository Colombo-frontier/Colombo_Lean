import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Nonnegative inverse hyperbolic cosine

An explicit real-valued inverse of `Real.cosh` on `[0,∞)`, used to define the
actual hyperboloid distance. Values below `1` are a total-function extension;
all inverse and order statements state their mathematical domain explicitly.
-/

namespace Geode

noncomputable def arcosh (x : ℝ) : ℝ :=
  Real.arsinh (Real.sqrt (x ^ 2 - 1))

theorem arcosh_nonneg (x : ℝ) : 0 ≤ arcosh x :=
  Real.arsinh_nonneg_iff.mpr (Real.sqrt_nonneg _)

@[simp] theorem arcosh_one : arcosh 1 = 0 := by simp [arcosh]

theorem sinh_arcosh (x : ℝ) :
    Real.sinh (arcosh x) = Real.sqrt (x ^ 2 - 1) := by
  simp [arcosh]

theorem cosh_arcosh {x : ℝ} (hx : 1 ≤ x) : Real.cosh (arcosh x) = x := by
  have hx0 : 0 ≤ x := by linarith
  have hx2 : 0 ≤ x ^ 2 - 1 := by nlinarith
  rw [arcosh, Real.cosh_arsinh, Real.sq_sqrt hx2]
  rw [show 1 + (x ^ 2 - 1) = x ^ 2 by ring, Real.sqrt_sq hx0]

theorem arcosh_cosh {x : ℝ} (hx : 0 ≤ x) : arcosh (Real.cosh x) = x := by
  apply Real.sinh_injective
  rw [sinh_arcosh, ← Real.sinh_sq]
  exact Real.sqrt_sq (Real.sinh_nonneg_iff.mpr hx)

theorem arcosh_eq_zero_iff {x : ℝ} (hx : 1 ≤ x) : arcosh x = 0 ↔ x = 1 := by
  constructor
  · intro h
    have hc := cosh_arcosh hx
    simpa [h] using hc.symm
  · rintro rfl
    exact arcosh_one

theorem arcosh_pos_iff {x : ℝ} (hx : 1 ≤ x) : 0 < arcosh x ↔ 1 < x := by
  constructor
  · intro h
    exact lt_of_le_of_ne hx (fun h' => by simp [← h'] at h)
  · intro h
    exact lt_of_le_of_ne (arcosh_nonneg x) (fun h' =>
      (ne_of_gt h) ((arcosh_eq_zero_iff hx).mp h'.symm))

theorem arcosh_le_arcosh_iff {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    arcosh x ≤ arcosh y ↔ x ≤ y := by
  have h := @Real.cosh_le_cosh (arcosh x) (arcosh y)
  rw [abs_of_nonneg (arcosh_nonneg x), abs_of_nonneg (arcosh_nonneg y),
    cosh_arcosh hx, cosh_arcosh hy] at h
  exact h.symm

theorem arcosh_lt_arcosh_iff {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    arcosh x < arcosh y ↔ x < y := by
  have h := @Real.cosh_lt_cosh (arcosh x) (arcosh y)
  rw [abs_of_nonneg (arcosh_nonneg x), abs_of_nonneg (arcosh_nonneg y),
    cosh_arcosh hx, cosh_arcosh hy] at h
  exact h.symm

theorem arcosh_inj {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    arcosh x = arcosh y ↔ x = y := by
  constructor
  · intro h
    have hc := congrArg Real.cosh h
    simpa [cosh_arcosh hx, cosh_arcosh hy] using hc
  · exact congrArg arcosh

theorem arcosh_le_iff_le_cosh {x r : ℝ} (hx : 1 ≤ x) (hr : 0 ≤ r) :
    arcosh x ≤ r ↔ x ≤ Real.cosh r := by
  simpa only [arcosh_cosh hr] using arcosh_le_arcosh_iff hx (Real.one_le_cosh r)

theorem le_arcosh_iff_cosh_le {x r : ℝ} (hx : 1 ≤ x) (hr : 0 ≤ r) :
    r ≤ arcosh x ↔ Real.cosh r ≤ x := by
  simpa only [arcosh_cosh hr] using arcosh_le_arcosh_iff (Real.one_le_cosh r) hx

theorem continuous_arcosh : Continuous arcosh := by
  unfold arcosh
  exact (((continuous_id.pow 2).sub continuous_const).sqrt).arsinh

theorem hasDerivAt_arcosh {x : ℝ} (hx : 1 < x) :
    HasDerivAt arcosh (Real.sqrt (x ^ 2 - 1))⁻¹ x := by
  have hx0 : 0 < x := by linarith
  have hrad : 0 < x ^ 2 - 1 := by nlinarith
  have hpoly : HasDerivAt (fun y : ℝ => y ^ 2 - 1) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).sub_const 1 using 1
    simp
  have hcomp := (hpoly.sqrt (ne_of_gt hrad)).arsinh
  have hsqrt : Real.sqrt (1 + Real.sqrt (x ^ 2 - 1) ^ 2) = x := by
    rw [Real.sq_sqrt hrad.le]
    rw [show 1 + (x ^ 2 - 1) = x ^ 2 by ring, Real.sqrt_sq hx0.le]
  convert hcomp using 1
  rw [smul_eq_mul, hsqrt]
  field_simp

theorem differentiableAt_arcosh {x : ℝ} (hx : 1 < x) :
    DifferentiableAt ℝ arcosh x := (hasDerivAt_arcosh hx).differentiableAt

theorem arcosh_eq_log {x : ℝ} (hx : 1 ≤ x) :
    arcosh x = Real.log (x + Real.sqrt (x ^ 2 - 1)) := by
  have hrad : 0 ≤ x ^ 2 - 1 := by nlinarith
  unfold arcosh Real.arsinh
  rw [Real.sq_sqrt hrad, show 1 + (x ^ 2 - 1) = x ^ 2 by ring,
    Real.sqrt_sq (by linarith : 0 ≤ x), add_comm]

theorem arcosh_strictMonoOn : StrictMonoOn arcosh (Set.Ici 1) := by
  intro x hx y hy hxy
  exact (arcosh_lt_arcosh_iff hx hy).mpr hxy

theorem arcosh_monotoneOn : MonotoneOn arcosh (Set.Ici 1) :=
  arcosh_strictMonoOn.monotoneOn

theorem contDiffAt_arcosh {n : ℕ∞} {x : ℝ} (hx : 1 < x) :
    ContDiffAt ℝ n arcosh x := by
  have hrad : x ^ 2 - 1 ≠ 0 := by nlinarith
  exact (((contDiffAt_id.pow 2).sub contDiffAt_const).sqrt hrad).arsinh

theorem contDiffOn_arcosh {n : ℕ∞} : ContDiffOn ℝ n arcosh (Set.Ioi 1) :=
  fun _ hx => (contDiffAt_arcosh hx).contDiffWithinAt

theorem deriv_arcosh {x : ℝ} (hx : 1 < x) :
    deriv arcosh x = (Real.sqrt (x ^ 2 - 1))⁻¹ := (hasDerivAt_arcosh hx).deriv

/-- The derivative of the inverse-cosh slope, in the form used by distance
Hessian computations away from the diagonal. -/
theorem hasDerivAt_arcosh_slope {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun y : ℝ => (Real.sqrt (y ^ 2 - 1))⁻¹)
      (-x / Real.sqrt (x ^ 2 - 1) ^ 3) x := by
  have hrad : 0 < x ^ 2 - 1 := by nlinarith
  have hpoly : HasDerivAt (fun y : ℝ => y ^ 2 - 1) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).sub_const 1 using 1
    simp
  have hsq : Real.sqrt (x ^ 2 - 1) ≠ 0 := (Real.sqrt_pos.mpr hrad).ne'
  convert (hpoly.sqrt hrad.ne').inv hsq using 1
  field_simp
  rw [show Real.sqrt (x ^ 2 - 1) ^ 3 =
    (x ^ 2 - 1) * Real.sqrt (x ^ 2 - 1) by rw [pow_succ, Real.sq_sqrt hrad.le]]
  ring

end Geode
