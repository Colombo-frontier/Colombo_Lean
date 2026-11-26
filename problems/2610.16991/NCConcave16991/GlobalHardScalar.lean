import NCConcave16991.ConePrimitives
import NCConcave16991.LocalizationStepSecond

/-! # Literal scalar gates and state corrections of Appendix E's global assembly -/

namespace NCConcave16991.GlobalHard

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory LocalizationScalar LocalizationStep LocalizationStepSecond
open scoped ContDiff Topology

def deltaGate : ℝ := 1 / 430000
def gamma : ℝ := 4300
def stateWeight : ℝ := 172
def radialSlope : ℝ := 32417

/-- The actual antiderivative p(t)=integral_0^t omega; its closed expression
uses the already verified integral radial profile. -/
def primitive : ℝ → ℝ := ConePrimitives.softPositive

theorem primitive_contDiff : ContDiff ℝ ∞ primitive := ConePrimitives.softPositive_contDiff
theorem primitive_hasDerivAt (t : ℝ) : HasDerivAt primitive (Real.smoothTransition t) t :=
  ConePrimitives.softPositive_hasDerivAt t
theorem primitive_zero {t : ℝ} (ht : t ≤ 0) : primitive t = 0 := ConePrimitives.softPositive_zero ht
theorem primitive_linear {t : ℝ} (ht : 1 ≤ t) : primitive t = t - 1 / 2 :=
  ConePrimitives.softPositive_linear ht

theorem primitive_eq_integral (t : ℝ) : primitive t = ∫ s in (0 : ℝ)..t, Real.smoothTransition s := by
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ ↦ primitive_hasDerivAt s) (Real.smoothTransition.continuous.intervalIntegrable 0 t)
  rw [primitive_zero (by norm_num : (0 : ℝ) ≤ 0), sub_zero] at hh
  exact hh.symm

def stateClamp (t : ℝ) : ℝ := primitive (t + 3) - primitive (t - 2) - 5 / 2
def stateClampDerivative (t : ℝ) : ℝ := Real.smoothTransition (t + 3) - Real.smoothTransition (t - 2)
def stateClampSecond (t : ℝ) : ℝ := deriv Real.smoothTransition (t + 3) - deriv Real.smoothTransition (t - 2)

theorem stateClamp_contDiff : ContDiff ℝ ∞ stateClamp := by
  unfold stateClamp
  exact ((primitive_contDiff.comp (by fun_prop)).sub (primitive_contDiff.comp (by fun_prop))).sub contDiff_const

theorem stateClamp_hasDerivAt (t : ℝ) : HasDerivAt stateClamp (stateClampDerivative t) t := by
  have hh := (((primitive_hasDerivAt (t + 3)).comp t ((hasDerivAt_id t).add_const 3)).sub
    ((primitive_hasDerivAt (t - 2)).comp t ((hasDerivAt_id t).sub_const 2))).sub_const (5 / 2)
  convert hh using 1 <;> first | rfl | dsimp [stateClampDerivative]; ring

theorem stateClampDerivative_hasDerivAt (t : ℝ) :
    HasDerivAt stateClampDerivative (stateClampSecond t) t := by
  have hc : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hd (x : ℝ) : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x :=
    (hc.differentiable (by simp) x).hasDerivAt
  have hh := ((hd (t + 3)).comp t ((hasDerivAt_id t).add_const 3)).sub
      ((hd (t - 2)).comp t ((hasDerivAt_id t).sub_const 2))
  convert hh using 1 <;> first | rfl | dsimp [stateClampSecond]; ring

theorem stateClamp_identity {t : ℝ} (hl : -2 ≤ t) (hr : t ≤ 2) : stateClamp t = t := by
  unfold stateClamp
  rw [primitive_linear (by linarith : 1 ≤ t + 3), primitive_zero (by linarith : t - 2 ≤ 0)]
  ring

theorem stateClamp_left {t : ℝ} (ht : t ≤ -3) : stateClamp t = -5 / 2 := by
  unfold stateClamp
  rw [primitive_zero (by linarith : t + 3 ≤ 0), primitive_zero (by linarith : t - 2 ≤ 0)]
  ring

theorem stateClamp_right {t : ℝ} (ht : 3 ≤ t) : stateClamp t = 5 / 2 := by
  unfold stateClamp
  rw [primitive_linear (by linarith : 1 ≤ t + 3), primitive_linear (by linarith : 1 ≤ t - 2)]
  ring

theorem stateClampDerivative_bounds (t : ℝ) : 0 ≤ stateClampDerivative t ∧ stateClampDerivative t ≤ 1 := by
  have hm := Real.smoothTransition.monotone (show t - 2 ≤ t + 3 by linarith)
  have h0 := Real.smoothTransition.nonneg (t - 2)
  have h1 := Real.smoothTransition.le_one (t + 3)
  dsimp [stateClampDerivative]
  constructor <;> linarith

theorem stateClamp_monotone : Monotone stateClamp := by
  apply monotone_of_deriv_nonneg (fun t ↦ (stateClamp_hasDerivAt t).differentiableAt)
  intro t
  rw [(stateClamp_hasDerivAt t).deriv]
  exact (stateClampDerivative_bounds t).1

theorem stateClamp_abs_bound (t : ℝ) : |stateClamp t| ≤ 5 / 2 := by
  by_cases hl : t ≤ -3
  · rw [stateClamp_left hl]; norm_num
  · by_cases hr : 3 ≤ t
    · rw [stateClamp_right hr]; norm_num
    · apply abs_le.mpr
      have ha := stateClamp_monotone (le_of_not_ge hl)
      have hb := stateClamp_monotone (le_of_not_ge hr)
      rw [stateClamp_left (by norm_num : (-3 : ℝ) ≤ -3)] at ha
      rw [stateClamp_right (by norm_num : (3 : ℝ) ≤ 3)] at hb
      exact ⟨by linarith, hb⟩

theorem stateClampSecond_abs_bound (t : ℝ) : |stateClampSecond t| ≤ 16 := by
  have ha := step_deriv_bounds (t + 3)
  have hb := step_deriv_bounds (t - 2)
  dsimp [stateClampSecond]
  apply abs_le.mpr
  constructor <;> linarith

def statePotential (t : ℝ) : ℝ :=
  -(radialSlope / 10) * (primitive (10 * t - 1) - primitive (10 * t - 10))
def statePotentialDerivative (t : ℝ) : ℝ :=
  -radialSlope * (Real.smoothTransition (10 * t - 1) - Real.smoothTransition (10 * t - 10))
def statePotentialSecond (t : ℝ) : ℝ :=
  -(10 * radialSlope) * (deriv Real.smoothTransition (10 * t - 1) - deriv Real.smoothTransition (10 * t - 10))

theorem statePotential_contDiff : ContDiff ℝ ∞ statePotential := by
  unfold statePotential
  exact contDiff_const.mul ((primitive_contDiff.comp (by fun_prop)).sub
    (primitive_contDiff.comp (by fun_prop)))

theorem statePotential_hasDerivAt (t : ℝ) : HasDerivAt statePotential (statePotentialDerivative t) t := by
  have hh := (((primitive_hasDerivAt (10 * t - 1)).comp t
    (((hasDerivAt_id t).const_mul 10).sub_const 1)).sub
    ((primitive_hasDerivAt (10 * t - 10)).comp t
      (((hasDerivAt_id t).const_mul 10).sub_const 10))).const_mul (-(radialSlope / 10))
  convert hh using 1 <;> first | rfl | dsimp [statePotentialDerivative]; ring

theorem statePotentialDerivative_hasDerivAt (t : ℝ) :
    HasDerivAt statePotentialDerivative (statePotentialSecond t) t := by
  have hc : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hd (x : ℝ) : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x :=
    (hc.differentiable (by simp) x).hasDerivAt
  have hh := (((hd (10 * t - 1)).comp t (((hasDerivAt_id t).const_mul 10).sub_const 1)).sub
    ((hd (10 * t - 10)).comp t (((hasDerivAt_id t).const_mul 10).sub_const 10))).const_mul (-radialSlope)
  convert hh using 1 <;> first | rfl | dsimp [statePotentialSecond]; ring

theorem statePotentialDerivative_bounds (t : ℝ) :
    -radialSlope ≤ statePotentialDerivative t ∧ statePotentialDerivative t ≤ 0 := by
  have hm := Real.smoothTransition.monotone (show 10 * t - 10 ≤ 10 * t - 1 by linarith)
  have h0 := Real.smoothTransition.nonneg (10 * t - 10)
  have h1 := Real.smoothTransition.le_one (10 * t - 1)
  dsimp [statePotentialDerivative, radialSlope]
  constructor <;> linarith

theorem statePotential_left {t : ℝ} (ht : t ≤ 1 / 10) : statePotential t = 0 := by
  unfold statePotential
  rw [primitive_zero (by linarith : 10 * t - 1 ≤ 0), primitive_zero (by linarith : 10 * t - 10 ≤ 0)]
  ring

theorem statePotential_right {t : ℝ} (ht : 11 / 10 ≤ t) : statePotential t = -(9 / 10) * radialSlope := by
  unfold statePotential
  rw [primitive_linear (by linarith : 1 ≤ 10 * t - 1), primitive_linear (by linarith : 1 ≤ 10 * t - 10)]
  ring

theorem statePotential_antitone : Antitone statePotential := by
  apply antitone_of_deriv_nonpos (fun t ↦ (statePotential_hasDerivAt t).differentiableAt)
  intro t
  rw [(statePotential_hasDerivAt t).deriv]
  exact (statePotentialDerivative_bounds t).2

theorem statePotential_bounds (t : ℝ) : -(9 / 10) * radialSlope ≤ statePotential t ∧ statePotential t ≤ 0 := by
  constructor
  · by_cases ht : 11 / 10 ≤ t
    · rw [statePotential_right ht]
    · have hh := statePotential_antitone (le_of_not_ge ht)
      rw [statePotential_right (le_refl (11 / 10 : ℝ))] at hh
      exact hh
  · by_cases ht : t ≤ 1 / 10
    · rw [statePotential_left ht]
    · have hh := statePotential_antitone (le_of_not_ge ht)
      rw [statePotential_left (le_refl (1 / 10 : ℝ))] at hh
      exact hh

theorem statePotentialSecond_abs_bound (t : ℝ) : |statePotentialSecond t| ≤ 160 * radialSlope := by
  have ha := step_deriv_bounds (10 * t - 1)
  have hb := step_deriv_bounds (10 * t - 10)
  rw [statePotentialSecond, abs_mul, abs_neg, abs_of_pos (by norm_num [radialSlope] : 0 < 10 * radialSlope)]
  have hh : |deriv Real.smoothTransition (10 * t - 1) - deriv Real.smoothTransition (10 * t - 10)| ≤ 16 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 10 * radialSlope by norm_num [radialSlope])
  nlinarith

end

end NCConcave16991.GlobalHard
