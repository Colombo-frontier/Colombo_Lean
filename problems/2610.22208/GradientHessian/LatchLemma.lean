import GradientHessian.LatchGradient

/-! Complete source-shaped scaled latch lemma, with one fixed absolute
constant and genuine Euclidean register norms. -/

noncomputable section
namespace GradientHessian.LatchLemma

open EuclideanRegisters LatchChain LatchLocalDerivatives LatchDerivativeSums LatchGradient

def latchConstant : ℝ := 1 + 128 * localConstant 1 +
  ∑ i ∈ Finset.range 4, (17 * localConstant i + 2 * edgeConstant i)

theorem latchConstant_bounds {j : ℕ} (hj : j ≤ 3) :
    8 * localConstant j ≤ latchConstant ∧ localConstant j ≤ latchConstant ∧
      2 * (8 * localConstant j + edgeConstant j) ≤ latchConstant ∧
      128 * localConstant 1 ≤ latchConstant := by
  have hnonneg : ∀ i : ℕ, 0 ≤ 17 * localConstant i + 2 * edgeConstant i := by
    intro i
    have hi := (localConstant_pos i).le
    have he := edgeConstant_nonneg i
    positivity
  have hs : 17 * localConstant j + 2 * edgeConstant j ≤
      ∑ i ∈ Finset.range 4, (17 * localConstant i + 2 * edgeConstant i) :=
    Finset.single_le_sum (f := fun i => 17 * localConstant i + 2 * edgeConstant i)
      (s := Finset.range 4) (fun i _ => hnonneg i) (Finset.mem_range.mpr (by omega))
  have hsum : 0 ≤ ∑ i ∈ Finset.range 4, (17 * localConstant i + 2 * edgeConstant i) :=
    Finset.sum_nonneg (fun i _ => hnonneg i)
  have hjpos := localConstant_pos j
  have h1pos := localConstant_pos 1
  have he := edgeConstant_nonneg j
  unfold latchConstant
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem latchConstant_pos : 0 < latchConstant := by
  have h := (latchConstant_bounds (j := 1) (by norm_num)).2.1
  exact (localConstant_pos 1).trans_le h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `n + 2` is the number of physical registers; the final radius is
`s * 2^(n+1)`. All derivative fields refer to actual iterated Frechet derivatives. -/
structure Bounds (n : ℕ) (s : ℝ) (v : Fin (n + 2) → E) : Prop where
  smooth_self : ContDiff ℝ 3 (self (n + 1) v (sourceScale s) 0)
  smooth_incoming : ContDiff ℝ 3 (fun U : Registers E (n + 2) => incoming s (v 0) (U 0))
  smooth_port : ContDiff ℝ 3 (port (n + 1) v (sourceScale s))
  incoming_values : ∀ U : Registers E (n + 2),
    0 ≤ incoming s (v 0) (U 0) ∧ incoming s (v 0) (U 0) ≤ 56 * s
  residual_values : ∀ U : Registers E (n + 2),
    -112 * sourceScale s (Fin.last (n + 1)) ≤ residual (n + 1) v (sourceScale s) U ∧
      residual (n + 1) v (sourceScale s) U ≤ 0
  incoming_derivatives : ∀ j ≤ 3, ∀ U : Registers E (n + 2),
    ‖iteratedFDeriv ℝ j (fun X : Registers E (n + 2) => incoming s (v 0) (X 0)) U‖ ≤
      latchConstant * s ^ (1 - (j : ℤ))
  residual_first : ∀ U : Registers E (n + 2),
    ‖iteratedFDeriv ℝ 1 (residual (n + 1) v (sourceScale s)) U‖ ≤
      latchConstant * Real.sqrt (n + 2)
  residual_second : ∀ U : Registers E (n + 2),
    ‖iteratedFDeriv ℝ 2 (residual (n + 1) v (sourceScale s)) U‖ ≤ latchConstant / s
  residual_third : ∀ U : Registers E (n + 2),
    ‖iteratedFDeriv ℝ 3 (residual (n + 1) v (sourceScale s)) U‖ ≤ latchConstant / s ^ 2
  port_derivatives : ∀ j, 1 ≤ j → j ≤ 3 → ∀ U : Registers E (n + 2),
    ‖iteratedFDeriv ℝ j (port (n + 1) v (sourceScale s)) U‖ ≤
      latchConstant / (sourceScale s (Fin.last (n + 1))) ^ j
  activation : ∀ l : ℝ, 0 ≤ l → ∀ U : Registers E (n + 2),
    ‖gradient (fun X => self (n + 1) v (sourceScale s) 0 X - incoming s (v 0) (X 0) -
      l * port (n + 1) v (sourceScale s) X) U‖ ≤ 1 →
        (∀ i, 7 / 8 ≤ u (sourceScale s i) (v i) (U i)) ∧ port (n + 1) v (sourceScale s) U = 1
  transition : ∀ (a z : E) (xi : ℝ), ‖a‖ = 1 → xi ≤ 1 / 2 →
    2 / 3 < LatchActivation.readout a z → LatchActivation.readout a z < 3 / 4 →
      1 < ‖(8 : ℝ) • z - (8 - xi) • fderiv ℝ (RadialSquash.squash 8) z a‖

/-- All assertions of manuscript `lem:latch`, with the source scale schedule,
at least two registers, and a constant independent of dimension, length and scales. -/
theorem latch_bounds (n : ℕ) (v : Fin (n + 2) → E) {s : ℝ} (hs : 1 ≤ s)
    (hv : ∀ i, ‖v i‖ = 1) : Bounds n s v := by
  have hs0 : 0 < s := by linarith
  have hr : ∀ i : Fin (n + 2), 0 < sourceScale s i := sourceScale_pos hs0
  refine {
    smooth_self := self_contDiff _ _ _ _
    smooth_incoming := (incoming_contDiff s (v 0)).comp (head E (n + 1)).contDiff
    smooth_port := port_contDiff _ _ _
    incoming_values := fun U => (source_value_bounds n v hs U).1
    residual_values := fun U => (source_value_bounds n v hs U).2
    incoming_derivatives := ?_
    residual_first := ?_
    residual_second := ?_
    residual_third := ?_
    port_derivatives := ?_
    activation := fun l hl U hg => source_activation n v hs hl hv U hg
    transition := fun a z xi ha hxi hu0 hu1 => LatchGeometry.transition_exclusion a z ha hxi hu0 hu1 }
  · intro j hj U
    apply (derivative_projection_le (0 : Fin (n + 2)) (incoming_contDiff s (v 0)) hj U).trans
    apply (incoming_derivative_bound hs0 (v 0) (U 0) (hv 0) hj).trans
    exact mul_le_mul_of_nonneg_right (latchConstant_bounds hj).1 (zpow_nonneg hs0.le _)
  · intro U
    have h := residual_first_derivative_bound (n + 1) v hs0 hv U
    have hc := mul_le_mul_of_nonneg_right
      (latchConstant_bounds (j := 1) (by norm_num)).2.2.2 (Real.sqrt_nonneg (n + 2))
    exact h.trans (by simpa only [Nat.cast_add, Nat.cast_one, add_assoc,
      show (1 : ℝ) + 1 = 2 by norm_num] using hc)
  · intro U
    have h := (residual_higher_derivative_bound (n + 1) v hs0 hv (n := 2)
      (by norm_num) (by norm_num) U).trans
      (mul_le_mul_of_nonneg_right (latchConstant_bounds (j := 2) (by norm_num)).2.2.1
        (zpow_nonneg hs0.le (1 - (2 : ℤ))))
    simpa only [Nat.cast_ofNat, show (1 : ℤ) - 2 = -1 by norm_num, zpow_neg_one,
      div_eq_mul_inv] using h
  · intro U
    have h := (residual_higher_derivative_bound (n + 1) v hs0 hv (n := 3)
      (by norm_num) (by norm_num) U).trans
      (mul_le_mul_of_nonneg_right (latchConstant_bounds (j := 3) (by norm_num)).2.2.1
        (zpow_nonneg hs0.le (1 - (3 : ℤ))))
    simpa only [Nat.cast_ofNat, show (1 : ℤ) - 3 = -2 by norm_num, zpow_neg, zpow_ofNat,
      div_eq_mul_inv] using h
  · intro j _ hj U
    exact (port_derivative_bound (n + 1) v (sourceScale s) (hr _) (hv _) hj U).trans
      (div_le_div_of_nonneg_right (latchConstant_bounds hj).2.1 (pow_nonneg (hr _).le _))

end GradientHessian.LatchLemma
