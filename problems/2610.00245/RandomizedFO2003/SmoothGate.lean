import RandomizedFO2003.Stationarity
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded

namespace RandomizedFO2003.Primitives

open Filter Set Function
open scoped Topology

theorem glue_hasDerivAt (x : ℝ) :
    HasDerivAt expNegInvGlue (x⁻¹ ^ 2 * expNegInvGlue x) x := by
  simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul 1 x

theorem transition_hasDerivAt (x : ℝ) :
    HasDerivAt Real.smoothTransition
      (((x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2) * expNegInvGlue x * expNegInvGlue (1 - x)) /
        (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2) x := by
  have hr := (glue_hasDerivAt (1 - x)).comp x ((hasDerivAt_const x 1).sub (hasDerivAt_id x))
  have h := (glue_hasDerivAt x).div ((glue_hasDerivAt x).add hr)
    (Real.smoothTransition.pos_denom x).ne'
  convert h using 1
  dsimp only [Function.comp_apply]
  ring

theorem transition_deriv_nonneg (x : ℝ) : 0 ≤ deriv Real.smoothTransition x := by
  rw [(transition_hasDerivAt x).deriv]
  exact div_nonneg
    (mul_nonneg (mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (expNegInvGlue.nonneg _))
      (expNegInvGlue.nonneg _)) (sq_nonneg _)

/-- The transition occurs strictly inside the required interval, so even the
closed support of every nonconstant derivative stays inside `(1/4, 1/2)`. -/
noncomputable def gate (x : ℝ) : ℝ := Real.smoothTransition (8 * x - 5 / 2)

theorem gate_contDiff (n : ℕ) : ContDiff ℝ n gate :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem gate_nonneg (x : ℝ) : 0 ≤ gate x := Real.smoothTransition.nonneg _
theorem gate_le_one (x : ℝ) : gate x ≤ 1 := Real.smoothTransition.le_one _

theorem gate_zero_of_le {x : ℝ} (hx : x ≤ 5 / 16) : gate x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem gate_one_of_le {x : ℝ} (hx : 7 / 16 ≤ x) : gate x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem gate_deriv (x : ℝ) : deriv gate x = deriv Real.smoothTransition (8 * x - 5 / 2) * 8 := by
  have ht := (transition_hasDerivAt (8 * x - 5 / 2))
  have ha : HasDerivAt (fun y : ℝ => 8 * y - 5 / 2) 8 x := by
    simpa using ((hasDerivAt_id x).const_mul 8).sub_const (5 / 2)
  have hg := ht.comp x ha
  rw [← ht.deriv] at hg
  exact hg.deriv

theorem gate_deriv_nonneg (x : ℝ) : 0 ≤ deriv gate x := by
  rw [gate_deriv]
  exact mul_nonneg (transition_deriv_nonneg _) (by norm_num)

theorem gate_monotone : Monotone gate :=
  monotone_of_deriv_nonneg ((gate_contDiff 1).differentiable (by norm_num)) gate_deriv_nonneg

theorem gate_deriv_zero_left {x : ℝ} (hx : x < 5 / 16) : deriv gate x = 0 := by
  have h : gate =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [gt_mem_nhds hx] with y hy
    exact gate_zero_of_le hy.le
  rw [h.deriv_eq, deriv_const]

theorem gate_deriv_zero_right {x : ℝ} (hx : 7 / 16 < x) : deriv gate x = 0 := by
  have h : gate =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [lt_mem_nhds hx] with y hy
    exact gate_one_of_le hy.le
  rw [h.deriv_eq, deriv_const]

theorem gate_deriv_support : support (deriv gate) ⊆ Icc (5 / 16 : ℝ) (7 / 16) := by
  intro x hx
  by_contra hn
  rcases not_and_or.mp hn with hleft | hright
  · exact hx (gate_deriv_zero_left (lt_of_not_ge hleft))
  · exact hx (gate_deriv_zero_right (lt_of_not_ge hright))

theorem gate_deriv_tsupport : tsupport (deriv gate) ⊆ Ioo (1 / 4 : ℝ) (1 / 2) := by
  have h := closure_minimal gate_deriv_support isClosed_Icc
  intro x hx
  have hb := h hx
  constructor <;> linarith [hb.1, hb.2]

theorem gate_deriv_compactSupport : HasCompactSupport (deriv gate) := by
  apply isCompact_Icc.of_isClosed_subset isClosed_closure
  exact closure_minimal gate_deriv_support isClosed_Icc

theorem gate_iteratedDeriv_compactSupport (k : ℕ) : HasCompactSupport (iteratedDeriv (k + 1) gate) := by
  induction k with
  | zero => simpa using gate_deriv_compactSupport
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv

/-- Every positive-order derivative has a finite numerical bound. In
particular this supplies all four constants required by the source lemma. -/
theorem gate_derivative_bound (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, |iteratedDeriv k gate x| ≤ C := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨C, hC⟩ := (gate_iteratedDeriv_compactSupport j).exists_bound_of_continuous
    ((gate_contDiff (j + 1)).continuous_iteratedDeriv (j + 1) le_rfl)
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  have hx : |iteratedDeriv (j + 1) gate x| ≤ C := by simpa only [Real.norm_eq_abs] using hC x
  exact hx.trans (le_max_left C 1)

noncomputable def flatGate : RandomizedFO2003.FlatGate where
  value := gate
  flat _ hx := gate_zero_of_le (by linarith)
  full _ hx := gate_one_of_le (by linarith)

end RandomizedFO2003.Primitives
