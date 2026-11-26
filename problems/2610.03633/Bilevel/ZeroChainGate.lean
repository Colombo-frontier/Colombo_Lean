import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-! The exact one-sided `exp(-1/x²)` gate and all of its flat jets. -/

noncomputable section
open Polynomial Real Filter Set
open scoped Topology

namespace Bilevel.ZeroChainGate

def gate (x : ℝ) : ℝ := if x ≤ 0 then 0 else expNegInvGlue (x ^ 2)

def jet (p : ℝ[X]) (x : ℝ) : ℝ := p.eval x⁻¹ * gate x

def next (p : ℝ[X]) : ℝ[X] := C 2 * X ^ 3 * p - X ^ 2 * derivative p

theorem gate_zero {x : ℝ} (hx : x ≤ 0) : gate x = 0 := by simp [gate, hx]

theorem gate_pos_formula {x : ℝ} (hx : 0 < x) : gate x = Real.exp (-(x⁻¹) ^ 2) := by
  simp only [gate, if_neg hx.not_le, expNegInvGlue, if_neg (sq_pos_of_pos hx).not_le, inv_pow]

theorem gate_nonneg (x : ℝ) : 0 ≤ gate x := by
  by_cases hx : x ≤ 0
  · simp [gate_zero hx]
  · rw [gate_pos_formula (lt_of_not_ge hx)]
    exact (Real.exp_pos _).le

theorem gate_le_one (x : ℝ) : gate x ≤ 1 := by
  by_cases hx : x ≤ 0
  · simp [gate_zero hx]
  · rw [gate_pos_formula (lt_of_not_ge hx)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))

theorem jet_zero (p : ℝ[X]) {x : ℝ} (hx : x ≤ 0) : jet p x = 0 := by
  simp [jet, gate_zero hx]

theorem tendsto_invpow_even_glue (n : ℕ) :
    Tendsto (fun x : ℝ => (x⁻¹) ^ n * expNegInvGlue (x ^ 2)) (𝓝 0) (𝓝 0) := by
  have hs : Tendsto (fun x : ℝ => x ^ 2) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_id.pow 2).tendsto (0 : ℝ)
  have hh := (expNegInvGlue.tendsto_polynomial_inv_mul_zero (X ^ n)).comp hs
  simp only [eval_pow, eval_X] at hh
  have hp := ((continuous_id.pow n).tendsto (0 : ℝ)).mul hh
  simp only [mul_zero] at hp
  convert hp using 1
  funext x
  by_cases hx : x = 0
  · subst x
    simp
  · field_simp
    ring

theorem tendsto_polynomial_even_glue (p : ℝ[X]) :
    Tendsto (fun x : ℝ => p.eval x⁻¹ * expNegInvGlue (x ^ 2)) (𝓝 0) (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | monomial n c =>
      simpa [Polynomial.eval_monomial, mul_assoc] using
        tendsto_const_nhds.mul (tendsto_invpow_even_glue n)
  | add p q hp hq => simpa only [eval_add, add_mul, add_zero] using hp.add hq

theorem tendsto_jet_zero (p : ℝ[X]) : Tendsto (jet p) (𝓝 0) (𝓝 0) := by
  change Tendsto (fun x : ℝ => p.eval x⁻¹ * gate x) (𝓝 0) (𝓝 0)
  simp only [gate, mul_ite, mul_zero]
  exact tendsto_const_nhds.if' (tendsto_polynomial_even_glue p)

theorem jet_hasDerivAt (p : ℝ[X]) (x : ℝ) : HasDerivAt (jet p) (jet (next p) x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [jet_zero _ hx.le]
    apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hx] with y hy
    exact jet_zero p hy.le
  · rw [jet_zero _ le_rfl, hasDerivAt_iff_tendsto_slope]
    refine ((tendsto_jet_zero (p * X)).mono_left inf_le_left).congr (fun x => ?_)
    simp [jet, gate_zero le_rfl, slope_def_field, div_eq_mul_inv, mul_right_comm]
  · have hd := ((p.hasDerivAt x⁻¹).mul (((hasDerivAt_id x⁻¹).pow 2).neg.exp)).comp x
      (hasDerivAt_inv hx.ne')
    convert hd.congr_of_eventuallyEq ?_ using 1
    · simp only [jet, next, eval_sub, eval_mul, eval_C, eval_pow, eval_X,
        gate_pos_formula hx, Function.comp_apply, id_eq]
      ring
    · filter_upwards [lt_mem_nhds hx] with y hy
      simp only [jet, gate_pos_formula hy, Function.comp_apply, id_eq]

theorem jet_differentiable (p : ℝ[X]) : Differentiable ℝ (jet p) :=
  fun x => (jet_hasDerivAt p x).differentiableAt

theorem jet_continuous (p : ℝ[X]) : Continuous (jet p) := (jet_differentiable p).continuous

theorem jet_contDiff {n : ℕ∞} (p : ℝ[X]) : ContDiff ℝ n (jet p) := by
  apply contDiff_all_iff_nat.mpr (fun k => ?_) n
  induction k generalizing p with
  | zero => exact contDiff_zero.mpr (jet_continuous p)
  | succ k ih =>
      rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = k + 1 from rfl]
      refine contDiff_succ_iff_deriv.mpr ⟨jet_differentiable p, by simp, ?_⟩
      convert ih (next p) using 2
      funext x
      exact (jet_hasDerivAt p x).deriv

theorem jet_one : jet 1 = gate := by
  funext x
  simp [jet]

theorem gate_contDiff {n : ℕ∞} : ContDiff ℝ n gate := by
  rw [← jet_one]
  exact jet_contDiff 1

theorem gate_hasDerivAt (x : ℝ) :
    HasDerivAt gate (2 * (x⁻¹) ^ 3 * gate x) x := by
  have h := jet_hasDerivAt 1 x
  rw [jet_one] at h
  simpa [jet, next] using h

def polynomialJet : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => next (polynomialJet n)

theorem gate_iteratedDeriv (n : ℕ) : iteratedDeriv n gate = jet (polynomialJet n) := by
  induction n with
  | zero => rw [iteratedDeriv_zero]; exact jet_one.symm
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      exact (jet_hasDerivAt (polynomialJet n) x).deriv

theorem gate_flat (n : ℕ) {x : ℝ} (hx : x ≤ 0) : iteratedDeriv n gate x = 0 := by
  rw [gate_iteratedDeriv]
  exact jet_zero _ hx

/-- Every polynomial-times-gate jet is uniformly bounded on the whole line. -/
theorem jet_bounded (p : ℝ[X]) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |jet p x| ≤ K := by
  obtain ⟨A, hA⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    (jet_continuous p).continuousOn
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    p.continuous.continuousOn
  refine ⟨max A 0 + max B 0, by positivity, fun x => ?_⟩
  by_cases hx : x ≤ 0
  · rw [jet_zero p hx, abs_zero]
    positivity
  have hx0 : 0 < x := lt_of_not_ge hx
  by_cases hx1 : x ≤ 1
  · have hb : |jet p x| ≤ A := by simpa only [Real.norm_eq_abs] using hA x ⟨hx0.le, hx1⟩
    exact hb.trans ((le_max_left A 0).trans (le_add_of_nonneg_right (le_max_right B 0)))
  · have hxinv : x⁻¹ ∈ Icc (0 : ℝ) 1 :=
      ⟨inv_nonneg.mpr hx0.le, (inv_le_one₀ hx0).mpr (le_of_not_ge hx1)⟩
    have hb : |p.eval x⁻¹| ≤ B := by simpa only [Real.norm_eq_abs] using hB x⁻¹ hxinv
    calc
      |jet p x| = |p.eval x⁻¹| * gate x := by rw [jet, abs_mul, abs_of_nonneg (gate_nonneg x)]
      _ ≤ |p.eval x⁻¹| := mul_le_of_le_one_right (abs_nonneg _) (gate_le_one x)
      _ ≤ B := hb
      _ ≤ max A 0 + max B 0 := by linarith [le_max_left B 0, le_max_right A 0]

theorem gate_derivative_bounded (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |iteratedDeriv n gate x| ≤ K := by
  rw [gate_iteratedDeriv]
  exact jet_bounded _

end Bilevel.ZeroChainGate
