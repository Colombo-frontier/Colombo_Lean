import NoisyZO.HardMinimizer
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The manuscript's explicit smooth radial cutoff

The lower-bound family uses `chi (‖x‖² / h²)`, where `chi` is one on
`(-∞, 1/4]` and zero on `[1, ∞)`.  We realize `chi` using mathlib's explicit
infinitely smooth transition function.  Thus the Lean construction now has
the precise scalar-composition form used by the derivative expansion in
Appendix A of the manuscript.

Derivative-size estimates are deliberately separated from the elementary
support, range, and smoothness facts proved here.
-/

open scoped ContDiff

namespace NoisyZO

noncomputable section

/-- A fixed `C^infinity` scalar cutoff equal to one on `(-∞, 1/4]` and zero
on `[1, ∞)`.  The affine rescaling sends these two transition points to one
and zero, respectively. -/
def smoothCutoffProfile (u : ℝ) : ℝ :=
  Real.smoothTransition ((4 / 3 : ℝ) * (1 - u))

theorem smoothCutoffProfile_contDiff {n : ℕ∞} :
    ContDiff ℝ n smoothCutoffProfile := by
  unfold smoothCutoffProfile
  fun_prop

/-- The scalar profile is `C∞`, not merely `Cⁿ` for a fixed finite `n`. -/
theorem smoothCutoffProfile_contDiff_infty :
    ContDiff ℝ ∞ smoothCutoffProfile := by
  rw [contDiff_infty]
  intro n
  exact smoothCutoffProfile_contDiff

theorem smoothCutoffProfile_nonneg (u : ℝ) :
    0 ≤ smoothCutoffProfile u := by
  exact Real.smoothTransition.nonneg _

theorem smoothCutoffProfile_le_one (u : ℝ) :
    smoothCutoffProfile u ≤ 1 := by
  exact Real.smoothTransition.le_one _

theorem smoothCutoffProfile_eq_one_of_le_quarter {u : ℝ}
    (hu : u ≤ 1 / 4) : smoothCutoffProfile u = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

theorem smoothCutoffProfile_eq_zero_of_one_le {u : ℝ}
    (hu : 1 ≤ u) : smoothCutoffProfile u = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  nlinarith

/-- The exact radial cutoff from the manuscript: `chi (‖x‖² / h²)`. -/
def radialCutoff (d : ℕ) (h : ℝ) (_hh : 0 < h) : Point d → ℝ :=
  fun x => smoothCutoffProfile (‖x‖ ^ 2 / h ^ 2)

theorem radialCutoff_contDiff (d : ℕ) (h : ℝ) (hh : 0 < h)
    {n : ℕ∞} :
    ContDiff ℝ n (radialCutoff d h hh) := by
  unfold radialCutoff
  exact smoothCutoffProfile_contDiff.comp
    ((contDiff_norm_sq ℝ).div_const (h ^ 2))

theorem radialCutoff_nonneg (d : ℕ) (h : ℝ) (hh : 0 < h)
    (x : Point d) :
    0 ≤ radialCutoff d h hh x := by
  exact smoothCutoffProfile_nonneg _

theorem radialCutoff_le_one (d : ℕ) (h : ℝ) (hh : 0 < h)
    (x : Point d) :
    radialCutoff d h hh x ≤ 1 := by
  exact smoothCutoffProfile_le_one _

theorem abs_radialCutoff_le_one (d : ℕ) (h : ℝ) (hh : 0 < h)
    (x : Point d) :
    |radialCutoff d h hh x| ≤ 1 := by
  rw [abs_of_nonneg (radialCutoff_nonneg d h hh x)]
  exact radialCutoff_le_one d h hh x

/-- The cutoff is identically one on the closed ball of radius `h / 2`. -/
theorem radialCutoff_eq_one_of_norm_le_half (d : ℕ) (h : ℝ) (hh : 0 < h)
    {x : Point d} (hx : ‖x‖ ≤ h / 2) :
    radialCutoff d h hh x = 1 := by
  apply smoothCutoffProfile_eq_one_of_le_quarter
  have hsq : 0 < h ^ 2 := sq_pos_of_pos hh
  apply (div_le_iff₀ hsq).2
  nlinarith [sq_nonneg (‖x‖ - h / 2), norm_nonneg x]

/-- The cutoff vanishes on and outside the sphere of radius `h`. -/
theorem radialCutoff_eq_zero_of_h_le_norm (d : ℕ) (h : ℝ) (hh : 0 < h)
    {x : Point d} (hx : h ≤ ‖x‖) :
    radialCutoff d h hh x = 0 := by
  apply smoothCutoffProfile_eq_zero_of_one_le
  have hsq : 0 < h ^ 2 := sq_pos_of_pos hh
  apply (le_div_iff₀ hsq).2
  nlinarith [sq_nonneg (‖x‖ - h), norm_nonneg x]

theorem radialCutoff_support (d : ℕ) (h : ℝ) (hh : 0 < h) :
    Function.support (radialCutoff d h hh) = Metric.ball 0 h := by
  ext x
  rw [Function.mem_support, Metric.mem_ball, dist_zero_right]
  unfold radialCutoff smoothCutoffProfile
  rw [Ne, Real.smoothTransition.zero_iff_nonpos, not_le]
  have hsq : 0 < h ^ 2 := sq_pos_of_pos hh
  constructor
  · intro hx
    have hquot : ‖x‖ ^ 2 / h ^ 2 < 1 := by nlinarith
    have hnormsq : ‖x‖ ^ 2 < h ^ 2 := (div_lt_one hsq).mp hquot
    nlinarith [norm_nonneg x]
  · intro hx
    have hnormsq : ‖x‖ ^ 2 < h ^ 2 := by nlinarith [norm_nonneg x]
    have hquot : ‖x‖ ^ 2 / h ^ 2 < 1 := (div_lt_one hsq).2 hnormsq
    nlinarith

/-- The construction is even, hence radial enough for the hypercube family. -/
theorem radialCutoff_neg (d : ℕ) (h : ℝ) (hh : 0 < h)
    (x : Point d) :
    radialCutoff d h hh (-x) = radialCutoff d h hh x := by
  simp [radialCutoff]

/-- Every hard hypothesis agrees with the common quadratic outside the cutoff ball. -/
theorem hardValue_radialCutoff_eq_norm_sq_of_h_le_norm
    {d : ℕ} (h : ℝ) (hh : 0 < h) (rho : ℝ)
    (s : Fin d → ℝ) {x : Point d} (hx : h ≤ ‖x‖) :
    hardValue (radialCutoff d h hh) rho s x = ‖x‖ ^ 2 := by
  exact hardValue_eq_norm_sq_of_cutoff_zero
    (radialCutoff d h hh) rho s x
    (radialCutoff_eq_zero_of_h_le_norm d h hh hx)

/-- With the explicit cutoff, the normalized sum of all neighboring squared
signals is bounded globally, not only after separately assuming that the
query lies in the cutoff support. -/
theorem normalized_summed_neighbor_signal_radialCutoff_le
    {d : ℕ} (hd : 0 < d) (c h : ℝ) (hh : 0 < h)
    (s : Fin d → ℝ) (hs : ∀ i, s i ^ 2 = 1) (x : Point d) :
    (∑ i : Fin d,
        (hardValue (radialCutoff d h hh) (c / Real.sqrt d) s x -
          hardValue (radialCutoff d h hh) (c / Real.sqrt d) (flip s i) x) ^ 2) ≤
      4 * c ^ 2 * h ^ 2 / d := by
  by_cases hx : h ≤ ‖x‖
  · rw [summed_neighbor_signal_sq (radialCutoff d h hh)
      (c / Real.sqrt d) s hs x]
    rw [radialCutoff_eq_zero_of_h_le_norm d h hh hx]
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
    positivity
  · exact normalized_summed_neighbor_signal_le hd
      (radialCutoff d h hh) c h (le_of_lt hh) s hs x
      (le_of_lt (lt_of_not_ge hx))
      (abs_radialCutoff_le_one d h hh x)

end

end NoisyZO
