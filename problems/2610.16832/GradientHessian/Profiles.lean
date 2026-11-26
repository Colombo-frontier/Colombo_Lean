import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! The literal clamped septic profile used in Sections 6 and 7 of the manuscript.
The derivatives below are derivatives of the actual piecewise function, including seams.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace GradientHessian.Profiles

def septic (x : ℝ) : ℝ := 35*x^4 - 84*x^5 + 70*x^6 - 20*x^7
def septic₁ (x : ℝ) : ℝ := 140*x^3 - 420*x^4 + 420*x^5 - 140*x^6
def septic₂ (x : ℝ) : ℝ := 420*x^2 - 1680*x^3 + 2100*x^4 - 840*x^5
def septic₃ (x : ℝ) : ℝ := 840*x - 5040*x^2 + 8400*x^3 - 4200*x^4

def step (x : ℝ) : ℝ := if x ≤ 0 then 0 else if x ≤ 1 then septic x else 1
def step₁ (x : ℝ) : ℝ := if x ≤ 0 then 0 else if x ≤ 1 then septic₁ x else 0
def step₂ (x : ℝ) : ℝ := if x ≤ 0 then 0 else if x ≤ 1 then septic₂ x else 0
def step₃ (x : ℝ) : ℝ := if x ≤ 0 then 0 else if x ≤ 1 then septic₃ x else 0

theorem septic_derivative (x : ℝ) : HasDerivAt septic (septic₁ x) x := by
  convert ((((hasDerivAt_id x).pow 4).const_mul 35).sub
    (((hasDerivAt_id x).pow 5).const_mul 84)).add
    (((hasDerivAt_id x).pow 6).const_mul 70) |>.sub
    (((hasDerivAt_id x).pow 7).const_mul 20) using 1
  dsimp [septic, septic₁]; ring

theorem septic₁_derivative (x : ℝ) : HasDerivAt septic₁ (septic₂ x) x := by
  convert ((((hasDerivAt_id x).pow 3).const_mul 140).sub
    (((hasDerivAt_id x).pow 4).const_mul 420)).add
    (((hasDerivAt_id x).pow 5).const_mul 420) |>.sub
    (((hasDerivAt_id x).pow 6).const_mul 140) using 1
  dsimp [septic₁, septic₂]; ring

theorem septic₂_derivative (x : ℝ) : HasDerivAt septic₂ (septic₃ x) x := by
  convert ((((hasDerivAt_id x).pow 2).const_mul 420).sub
    (((hasDerivAt_id x).pow 3).const_mul 1680)).add
    (((hasDerivAt_id x).pow 4).const_mul 2100) |>.sub
    (((hasDerivAt_id x).pow 5).const_mul 840) using 1
  dsimp [septic₂, septic₃]; ring

theorem septic₁_factored (x : ℝ) : septic₁ x = 140*x^3*(1-x)^3 := by
  dsimp [septic₁]; ring

theorem septic_reflection (x : ℝ) : septic x + septic (1-x) = 1 := by
  dsimp [septic]; ring

private theorem glue_derivative {f g f' g' : ℝ → ℝ} {a : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hval : f a = g a) (hder : f' a = g' a) (x : ℝ) :
    HasDerivAt (fun t => if t ≤ a then f t else g t)
      (if x ≤ a then f' x else g' x) x := by
  rcases lt_trichotomy x a with h | rfl | h
  · simp only [if_pos h.le]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds h] with t ht
    exact if_pos ht.le
  · simp only [le_refl, if_true]
    have hl : HasDerivWithinAt (fun t => if t ≤ x then f t else g t) (f' x) (Iic x) x :=
      (hf x).hasDerivWithinAt.congr_of_mem (fun t ht => if_pos ht) (by simp)
    have hr : HasDerivWithinAt (fun t => if t ≤ x then f t else g t) (f' x) (Ici x) x := by
      rw [hder]
      apply (hg x).hasDerivWithinAt.congr_of_mem _ le_rfl
      intro t ht
      by_cases htx : t ≤ x
      · have : t = x := le_antisymm htx ht
        subst t
        simpa using hval
      · exact if_neg htx
    have hh := hl.union hr
    rw [Iic_union_Ici] at hh
    exact hh.hasDerivAt (Filter.univ_mem)
  · simp only [if_neg (not_le.mpr h)]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds h] with t ht
    exact if_neg (not_le.mpr ht)

theorem step_derivative (x : ℝ) : HasDerivAt step (step₁ x) x := by
  apply glue_derivative (fun x => hasDerivAt_const x 0)
    (glue_derivative septic_derivative (fun x => hasDerivAt_const x 1) (by norm_num [septic]) (by norm_num [septic₁]))
    <;> norm_num [septic, septic₁]

theorem step₁_derivative (x : ℝ) : HasDerivAt step₁ (step₂ x) x := by
  apply glue_derivative (fun x => hasDerivAt_const x 0)
    (glue_derivative septic₁_derivative (fun x => hasDerivAt_const x 0) (by norm_num [septic₁]) (by norm_num [septic₂]))
    <;> norm_num [septic₁, septic₂]

theorem step₂_derivative (x : ℝ) : HasDerivAt step₂ (step₃ x) x := by
  apply glue_derivative (fun x => hasDerivAt_const x 0)
    (glue_derivative septic₂_derivative (fun x => hasDerivAt_const x 0) (by norm_num [septic₂]) (by norm_num [septic₃]))
    <;> norm_num [septic₂, septic₃]

theorem deriv_step : deriv step = step₁ := deriv_eq step_derivative
theorem deriv_step₁ : deriv step₁ = step₂ := deriv_eq step₁_derivative
theorem deriv_step₂ : deriv step₂ = step₃ := deriv_eq step₂_derivative

theorem continuous_step₃ : Continuous step₃ := by
  have hp : Continuous septic₃ := by unfold septic₃; fun_prop
  have hi : Continuous (fun x : ℝ => if x ≤ 1 then septic₃ x else 0) :=
    hp.if_le continuous_const continuous_id continuous_const (by intro x hx; rw [hx]; norm_num [septic₃])
  exact continuous_const.if_le hi continuous_id continuous_const
    (by intro x hx; rw [hx]; norm_num [septic₃])

theorem contDiff_step : ContDiff ℝ 3 step := by
  have h₂ : ContDiff ℝ 1 step₂ := contDiff_one_iff_deriv.mpr
    ⟨fun x => (step₂_derivative x).differentiableAt, by rw [deriv_step₂]; exact continuous_step₃⟩
  have h₁ : ContDiff ℝ 2 step₁ := by
    rw [show (2 : WithTop ℕ∞) = 1+1 by norm_num, contDiff_succ_iff_deriv, deriv_step₁]
    exact ⟨fun x => (step₁_derivative x).differentiableAt, by simp, h₂⟩
  rw [show (3 : WithTop ℕ∞) = 2+1 by norm_num, contDiff_succ_iff_deriv, deriv_step]
  exact ⟨fun x => (step_derivative x).differentiableAt, by simp, h₁⟩

theorem step_nonpos {x : ℝ} (hx : x ≤ 0) : step x = 0 := by simp [step, hx]
theorem step_ge_one {x : ℝ} (hx : 1 ≤ x) : step x = 1 := by
  by_cases h : x ≤ 1
  · have : x = 1 := le_antisymm h hx
    subst x; norm_num [step, septic]
  · simp [step, h, show ¬x ≤ 0 by linarith]

theorem step_eq_septic {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) : step x = septic x := by
  by_cases h : x ≤ 0
  · have : x = 0 := le_antisymm h hx
    subst x; norm_num [step, septic]
  · simp [step, h, hx']

theorem step_monotone : Monotone step := by
  apply monotone_of_hasDerivAt_nonneg step_derivative
  intro x
  dsimp [step₁]
  split_ifs with h h'
  · exact le_rfl
  · rw [septic₁_factored]
    exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (le_of_lt (not_le.mp h)) _))
      (pow_nonneg (sub_nonneg.mpr h') _)
  · exact le_rfl

theorem step_bounds (x : ℝ) : 0 ≤ step x ∧ step x ≤ 1 := by
  constructor
  · by_cases h : x ≤ 0
    · rw [step_nonpos h]
    · have := step_monotone (le_of_lt (not_le.mp h))
      simpa only [step_nonpos (le_refl 0)] using this
  · by_cases h : 1 ≤ x
    · rw [step_ge_one h]
    · have := step_monotone (le_of_lt (not_le.mp h))
      simpa only [step_ge_one (le_refl 1)] using this

theorem flat_seams :
    step₁ 0 = 0 ∧ step₁ 1 = 0 ∧ step₂ 0 = 0 ∧ step₂ 1 = 0 ∧
    step₃ 0 = 0 ∧ step₃ 1 = 0 := by
  norm_num [step₁, step₂, step₃, septic₁, septic₂, septic₃]

theorem derivatives_flat_outside {x : ℝ} (hx : x ≤ 0 ∨ 1 ≤ x) :
    deriv step x = 0 ∧ deriv (deriv step) x = 0 ∧
      deriv (deriv (deriv step)) x = 0 := by
  rw [deriv_step, deriv_step₁, deriv_step₂]
  rcases hx with hx | hx
  · simp [step₁, step₂, step₃, hx]
  · by_cases h : x ≤ 1
    · have : x = 1 := le_antisymm h hx
      subst x; norm_num [step₁, step₂, step₃, septic₁, septic₂, septic₃]
    · simp [step₁, step₂, step₃, h, show ¬x ≤ 0 by linarith]

theorem derivative_bounds (x : ℝ) : 0 ≤ deriv step x ∧ deriv step x ≤ 35/16 := by
  rw [deriv_step]
  by_cases h₀ : x ≤ 0
  · norm_num [step₁, h₀]
  by_cases h₁ : x ≤ 1
  · simp only [step₁, if_neg h₀, if_pos h₁, septic₁_factored]
    have hn : 0 ≤ x * (1-x) := mul_nonneg (le_of_lt (not_le.mp h₀)) (sub_nonneg.mpr h₁)
    have hu : x * (1-x) ≤ (1/4 : ℝ) := by nlinarith [sq_nonneg (x-1/2)]
    have hc : (x * (1-x))^3 ≤ (1/4 : ℝ)^3 := by gcongr
    constructor
    · exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (le_of_lt (not_le.mp h₀)) _))
        (pow_nonneg (sub_nonneg.mpr h₁) _)
    · nlinarith [show 140*x^3*(1-x)^3 = 140*(x*(1-x))^3 by ring]
  · norm_num [step₁, h₀, h₁]

/-- The numerical/self gate and completion selector are the exact profiles in the source. -/
def chi (u : ℝ) : ℝ := step (4*u-1)
def varpi (u : ℝ) : ℝ := step (12*(u-2/3))

theorem contDiff_chi : ContDiff ℝ 3 chi := by
  exact contDiff_step.comp (by fun_prop)

theorem contDiff_varpi : ContDiff ℝ 3 varpi := by
  exact contDiff_step.comp (by fun_prop)

theorem chi_bounds (u : ℝ) : 0 ≤ chi u ∧ chi u ≤ 1 := step_bounds _
theorem varpi_bounds (u : ℝ) : 0 ≤ varpi u ∧ varpi u ≤ 1 := step_bounds _

theorem chi_zero {u : ℝ} (hu : u ≤ 1/4) : chi u = 0 :=
  step_nonpos (by linarith)
theorem chi_one {u : ℝ} (hu : 1/2 ≤ u) : chi u = 1 :=
  step_ge_one (by linarith)
theorem varpi_zero {u : ℝ} (hu : u ≤ 2/3) : varpi u = 0 :=
  step_nonpos (by linarith)
theorem varpi_one {u : ℝ} (hu : 3/4 ≤ u) : varpi u = 1 :=
  step_ge_one (by linarith)

theorem chi_derivative (u : ℝ) : HasDerivAt chi (4*step₁ (4*u-1)) u := by
  convert (step_derivative (4*u-1)).comp u
    (((hasDerivAt_id u).const_mul 4).sub_const 1) using 1
  simp [chi, mul_comm]

theorem chi_derivative_bound (u : ℝ) : |deriv chi u| ≤ 12 := by
  rw [(chi_derivative u).deriv]
  have hb := derivative_bounds (4*u-1)
  rw [deriv_step] at hb
  rw [abs_of_nonneg (mul_nonneg (by norm_num) hb.1)]
  linarith [hb.2]

end GradientHessian.Profiles
