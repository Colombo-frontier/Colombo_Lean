import NCConcave16991.LocalizationStep
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Numerical second derivative of the actual exponential cutoff

All estimates are derived from the explicit exponential function. The
polynomial-times-exponential terms are bounded at their analytic maxima.
The final gate is the actual `omega((5t-1)/4)` from Appendix E.
-/

namespace NCConcave16991.LocalizationStepSecond

open LocalizationScalar LocalizationStep Set
open scoped ContDiff Topology

theorem stepSecond_hasDerivAt {t : ℝ} (ht : t ≠ 0) (h1 : 1 - t ≠ 0) :
    HasDerivAt (deriv Real.smoothTransition)
      (Real.smoothTransition t * (1 - Real.smoothTransition t) *
        ((1 - 2 * Real.smoothTransition t) * (t⁻¹ ^ 2 + (1 - t)⁻¹ ^ 2) ^ 2 -
          2 * t⁻¹ ^ 3 + 2 * (1 - t)⁻¹ ^ 3)) t := by
  have hA : HasDerivAt (fun s : ℝ => s⁻¹ ^ 2 + (1 - s)⁻¹ ^ 2)
      (-2 * t⁻¹ ^ 3 + 2 * (1 - t)⁻¹ ^ 3) t := by
    have hh := ((hasDerivAt_inv ht).pow 2).add
      ((((hasDerivAt_const t 1).sub (hasDerivAt_id t)).inv h1).pow 2)
    refine hh.congr_deriv ?_
    dsimp
    field_simp
    ring
  have hω := step_hasDerivAt t
  have hh := (hω.mul ((hasDerivAt_const t 1).sub hω)).mul hA
  have he : deriv Real.smoothTransition = fun s : ℝ =>
      Real.smoothTransition s * (1 - Real.smoothTransition s) *
        (s⁻¹ ^ 2 + (1 - s)⁻¹ ^ 2) := funext step_deriv
  rw [he]
  refine hh.congr_deriv ?_
  dsimp
  ring

theorem stepSecond_formula {t : ℝ} (ht : t ≠ 0) (h1 : 1 - t ≠ 0) :
    deriv (deriv Real.smoothTransition) t =
      Real.smoothTransition t * (1 - Real.smoothTransition t) *
        ((1 - 2 * Real.smoothTransition t) * (t⁻¹ ^ 2 + (1 - t)⁻¹ ^ 2) ^ 2 -
          2 * t⁻¹ ^ 3 + 2 * (1 - t)⁻¹ ^ 3) := (stepSecond_hasDerivAt ht h1).deriv

/-- The elementary global maximum of `u^k exp(2-u)` on nonnegative inputs. -/
theorem pow_exp_max (k : ℕ) (hk : 1 ≤ k) (u : ℝ) (hu : 0 ≤ u) :
    u ^ k * Real.exp (2 - u) ≤ (k : ℝ) ^ k * Real.exp (2 - k) := by
  let f : ℝ → ℝ := fun x => x ^ k * Real.exp (2 - x)
  have hd (x : ℝ) : HasDerivAt f
      (x ^ (k - 1) * ((k : ℝ) - x) * Real.exp (2 - x)) x := by
    have hh := ((hasDerivAt_id x).pow k).mul
      (((hasDerivAt_const x 2).sub (hasDerivAt_id x)).exp)
    change HasDerivAt f _ x at hh
    refine hh.congr_deriv ?_
    have hp : x ^ k = x ^ (k - 1) * x := by
      rw [← pow_succ, Nat.sub_add_cancel hk]
    dsimp
    rw [hp]
    ring
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  by_cases huk : u ≤ k
  · have hmono : MonotoneOn f (Icc 0 k) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (k : ℝ)) hc.continuousOn
      · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
      · intro x hx
        have hx' : x ∈ Icc (0 : ℝ) k := interior_subset hx
        rw [(hd x).deriv]
        exact mul_nonneg (mul_nonneg (pow_nonneg hx'.1 _) (sub_nonneg.mpr hx'.2))
          (Real.exp_pos _).le
    exact hmono ⟨hu, huk⟩ ⟨by positivity, le_refl _⟩ huk
  · have hanti : AntitoneOn f (Ici k) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici (k : ℝ)) hc.continuousOn
      · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
      · intro x hx
        have hx' : (k : ℝ) ≤ x := interior_subset hx
        have hx0 : 0 ≤ x := (Nat.cast_nonneg k).trans hx'
        rw [(hd x).deriv]
        apply mul_nonpos_of_nonpos_of_nonneg _ (Real.exp_pos _).le
        exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hx0 _)
          (sub_nonpos.mpr hx')
    exact hanti (show (k : ℝ) ∈ Ici (k : ℝ) from by simp) (le_of_not_ge huk) (le_of_not_ge huk)

theorem fourth_exp_bound {u : ℝ} (hu : 2 ≤ u) : u ^ 4 * Real.exp (2 - u) ≤ 42 := by
  have hh := pow_exp_max 4 (by norm_num) u (by linarith)
  have he : (5 / 2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have he0 : 0 < Real.exp 1 := Real.exp_pos _
  have hexp : Real.exp (2 - (4 : ℕ)) = 1 / Real.exp 1 ^ 2 := by
    rw [show (2 : ℝ) - (4 : ℕ) = -(1 + 1) by norm_num, Real.exp_neg, Real.exp_add]
    simp only [pow_two, one_div, mul_inv]
  rw [hexp] at hh
  simp only [Nat.cast_ofNat, show (4 : ℝ) ^ 4 = 256 by norm_num] at hh
  have hb : 256 / Real.exp 1 ^ 2 ≤ (42 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < Real.exp 1 ^ 2)).mpr
    nlinarith
  exact hh.trans (by simpa only [div_eq_mul_inv, one_mul] using hb)

theorem third_exp_bound {u : ℝ} (hu : 2 ≤ u) : u ^ 3 * Real.exp (2 - u) ≤ 11 := by
  have hh := pow_exp_max 3 (by norm_num) u (by linarith)
  have he : (5 / 2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hexp : Real.exp (2 - (3 : ℕ)) = (Real.exp 1)⁻¹ := by norm_num [Real.exp_neg]
  rw [hexp] at hh
  simp only [Nat.cast_ofNat, show (3 : ℝ) ^ 3 = 27 by norm_num] at hh
  have hb : 27 / Real.exp 1 ≤ (11 : ℝ) := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith
  exact hh.trans (by simpa only [div_eq_mul_inv] using hb)

theorem stepSecond_bound_half {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2) :
    |deriv (deriv Real.smoothTransition) t| ≤ 128 := by
  let w := Real.smoothTransition t
  let u := t⁻¹
  let v := (1 - t)⁻¹
  have h1 : 0 < 1 - t := by linarith
  have hu : 2 ≤ u := by
    dsimp [u]
    rw [inv_eq_one_div, le_div_iff₀ ht]
    linarith
  have hv : 0 ≤ v ∧ v ≤ 2 := by
    dsimp [v]
    constructor
    · positivity
    · rw [inv_eq_one_div, div_le_iff₀ h1]
      linarith
  have hw0 : 0 ≤ w := Real.smoothTransition.nonneg t
  have hw1 : w ≤ 1 := Real.smoothTransition.le_one t
  have hwc : 0 ≤ w * (1 - w) := mul_nonneg hw0 (sub_nonneg.mpr hw1)
  have hwexp : w * (1 - w) ≤ Real.exp (2 - u) := by
    have hh := step_le_exp ht ht2
    dsimp [u, w] at *
    nlinarith [sq_nonneg (Real.smoothTransition t)]
  have hwabs : |1 - 2 * w| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hv2 : v ^ 2 ≤ 4 := by nlinarith
  have hv3 : v ^ 3 ≤ 8 := by nlinarith [mul_nonneg (sub_nonneg.mpr hv.2) (sq_nonneg (v + 2))]
  have hAsq : (u ^ 2 + v ^ 2) ^ 2 ≤ (u ^ 2 + 4) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
  have hfirst : |(1 - 2 * w) * (u ^ 2 + v ^ 2) ^ 2| ≤ (u ^ 2 + 4) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (u ^ 2 + v ^ 2))]
    exact (mul_le_mul_of_nonneg_right hwabs (sq_nonneg _)).trans (by simpa using hAsq)
  have hpoly : |(1 - 2 * w) * (u ^ 2 + v ^ 2) ^ 2 - 2 * u ^ 3 + 2 * v ^ 3| ≤
      u ^ 4 + 2 * u ^ 3 + 8 * u ^ 2 + 32 := by
    have htri1 := abs_sub ((1 - 2 * w) * (u ^ 2 + v ^ 2) ^ 2) (2 * u ^ 3)
    have htri2 := abs_add_le ((1 - 2 * w) * (u ^ 2 + v ^ 2) ^ 2 - 2 * u ^ 3) (2 * v ^ 3)
    rw [abs_of_nonneg (by positivity : 0 ≤ 2 * u ^ 3)] at htri1
    rw [abs_of_nonneg (by positivity : 0 ≤ 2 * v ^ 3)] at htri2
    nlinarith
  have h4 := fourth_exp_bound hu
  have h3 := third_exp_bound hu
  have h2 := sq_exp_bound hu
  have h0 : Real.exp (2 - u) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (show 2 - u ≤ 0 by linarith)
  have hmul := mul_le_mul hwexp hpoly (abs_nonneg _) (Real.exp_pos _).le
  rw [stepSecond_formula ht.ne' h1.ne', abs_mul,
    abs_of_nonneg (show 0 ≤ Real.smoothTransition t * (1 - Real.smoothTransition t) from hwc)]
  change w * (1 - w) * |(1 - 2 * w) * (u ^ 2 + v ^ 2) ^ 2 - 2 * u ^ 3 + 2 * v ^ 3| ≤ _
  nlinarith

theorem stepSecond_abs_symmetry {t : ℝ} (ht : t ≠ 0) (h1 : 1 - t ≠ 0) :
    |deriv (deriv Real.smoothTransition) (1 - t)| =
      |deriv (deriv Real.smoothTransition) t| := by
  rw [stepSecond_formula h1 (by simpa using ht), stepSecond_formula ht h1]
  rw [show 1 - (1 - t) = t by ring]
  have he : Real.smoothTransition (1 - t) = 1 - Real.smoothTransition t := by
    linarith [step_symmetry t]
  rw [he]
  have hh : (1 - Real.smoothTransition t) * (1 - (1 - Real.smoothTransition t)) *
      ((1 - 2 * (1 - Real.smoothTransition t)) * ((1 - t)⁻¹ ^ 2 + t⁻¹ ^ 2) ^ 2 -
        2 * (1 - t)⁻¹ ^ 3 + 2 * t⁻¹ ^ 3) =
      -(Real.smoothTransition t * (1 - Real.smoothTransition t) *
        ((1 - 2 * Real.smoothTransition t) * (t⁻¹ ^ 2 + (1 - t)⁻¹ ^ 2) ^ 2 -
          2 * t⁻¹ ^ 3 + 2 * (1 - t)⁻¹ ^ 3)) := by ring
  rw [hh, abs_neg]

/-- Exact global numeric estimate, with the endpoint derivatives included. -/
theorem stepSecond_bound (t : ℝ) : |deriv (deriv Real.smoothTransition) t| ≤ 128 := by
  by_cases ht0 : t ≤ 0
  · have hz : deriv Real.smoothTransition t = 0 := by
      rw [step_deriv, Real.smoothTransition.zero_of_nonpos ht0]
      ring
    have hm : IsLocalMin (deriv Real.smoothTransition) t := by
      apply IsMinOn.isLocalMin (s := univ)
      · intro s _
        rw [hz]
        exact (step_deriv_bounds s).1
      · exact Filter.univ_mem
    rw [hm.deriv_eq_zero]
    norm_num
  · by_cases ht1 : 1 ≤ t
    · have hz : deriv Real.smoothTransition t = 0 := by
        rw [step_deriv, Real.smoothTransition.one_of_one_le ht1]
        ring
      have hm : IsLocalMin (deriv Real.smoothTransition) t := by
        apply IsMinOn.isLocalMin (s := univ)
        · intro s _
          rw [hz]
          exact (step_deriv_bounds s).1
        · exact Filter.univ_mem
      rw [hm.deriv_eq_zero]
      norm_num
    · by_cases hh : t ≤ 1 / 2
      · exact stepSecond_bound_half (lt_of_not_ge ht0) hh
      · rw [← stepSecond_abs_symmetry (ne_of_gt (lt_of_not_ge ht0)) (by linarith)]
        exact stepSecond_bound_half (by linarith) (by linarith)

theorem gate_deriv (t : ℝ) : deriv gate t = (5 / 4) * deriv Real.smoothTransition ((5 * t - 1) / 4) := by
  have hh := (step_hasDerivAt ((5 * t - 1) / 4)).comp t
    ((((hasDerivAt_id t).const_mul 5).sub_const 1).div_const 4)
  change HasDerivAt gate _ t at hh
  rw [hh.deriv, ← step_deriv]
  ring

theorem gate_deriv_bound (t : ℝ) : 0 ≤ deriv gate t ∧ deriv gate t ≤ 10 := by
  rw [gate_deriv]
  have hh := step_deriv_bounds ((5 * t - 1) / 4)
  constructor <;> nlinarith

theorem gateSecond_deriv (t : ℝ) : deriv (deriv gate) t =
    (25 / 16) * deriv (deriv Real.smoothTransition) ((5 * t - 1) / 4) := by
  have hc : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hg : Differentiable ℝ (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp hc).2.differentiable (by simp)
  have hh := ((hg ((5 * t - 1) / 4)).hasDerivAt.comp t
    ((((hasDerivAt_id t).const_mul 5).sub_const 1).div_const 4)).const_mul (5 / 4 : ℝ)
  have he : deriv gate = fun t => (5 / 4) * deriv Real.smoothTransition ((5 * t - 1) / 4) := funext gate_deriv
  change HasDerivAt (fun s => (5 / 4 : ℝ) * deriv Real.smoothTransition ((5 * s - 1) / 4)) _ t at hh
  rw [he]
  rw [hh.deriv]
  ring

/-- The actual scalar gate from the paper has globally bounded Hessian 200. -/
theorem gateSecond_bound (t : ℝ) : |deriv (deriv gate) t| ≤ 200 := by
  rw [gateSecond_deriv, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 25 / 16)]
  have hh := stepSecond_bound ((5 * t - 1) / 4)
  nlinarith

end NCConcave16991.LocalizationStepSecond
