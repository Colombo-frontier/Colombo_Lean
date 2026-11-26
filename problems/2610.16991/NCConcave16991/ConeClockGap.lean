import NCConcave16991.ConeRadial
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Actual cone clocks, gates, value expression, and initial-gap estimate

Every scalar/vector term is the literal Section D formula, using the
concrete density and radial guard from the companion modules. The global
value expression is defined explicitly; its dual-ball maximization identity
is separate from the gap estimate proved here.
-/

namespace NCConcave16991.ConeClockGap

open ConePrimitives ConeRadial Set
open scoped BigOperators InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def perpendicular (v u : E) : E := u - ⟪u, v⟫_ℝ • v

noncomputable def clock (q : ℝ) (v z u : E) : ℝ :=
  Real.sqrt (1 + ‖u‖ ^ 2) - 1 + ‖u‖ ^ 2 / (2 * q) -
    10 * theta (⟪u, v⟫_ℝ - Real.sqrt (1 + ‖perpendicular v u‖ ^ 2) +
      4 * latch ⟪zeta z, v⟫_ℝ)

noncomputable def exitGate (q : ℝ) (v u : E) : ℝ :=
  exitStep ((⟪u, v⟫_ℝ - Real.sqrt (q ^ 2 + ‖perpendicular v u‖ ^ 2)) / q)

theorem exitGate_bounds (q : ℝ) (v u : E) : 0 ≤ exitGate q v u ∧ exitGate q v u ≤ 1 :=
  ⟨omega_nonneg _, omega_le_one _⟩

theorem clock_zero (q : ℝ) (v : E) : clock q v 0 0 = 0 := by
  simp only [clock, perpendicular, inner_zero_left, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    add_zero, zero_smul, sub_self, Real.sqrt_one, zero_div, zeta_zero]
  rw [latch_zero (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  norm_num [theta_zero (by norm_num : (-1 : ℝ) ≤ 0)]

theorem exitGate_zero {q : ℝ} (hq : 0 < q) (v : E) : exitGate q v 0 = 0 := by
  unfold exitGate perpendicular
  simp only [inner_zero_left, zero_smul, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
  rw [Real.sqrt_sq hq.le, zero_sub, neg_div, div_self hq.ne']
  exact exitStep_zero (by norm_num)

/-- Actual clock coercive lower bound, obtained by completing its quadratic
square, with no stationarity or smoothness assumption. -/
theorem clock_lower_bound {q : ℝ} (hq : 1 ≤ q) (v : E) (hv : ‖v‖ = 1) (z u : E) :
    -91 * q ≤ clock q v z u := by
  have hq0 : 0 < q := by linarith
  have ht := abs_real_inner_le_norm u v
  rw [hv, mul_one] at ht
  have ht' := le_abs_self ⟪u, v⟫_ℝ
  have hH := latch_le_one ⟪zeta z, v⟫_ℝ
  let a := ⟪u, v⟫_ℝ - Real.sqrt (1 + ‖perpendicular v u‖ ^ 2) + 4 * latch ⟪zeta z, v⟫_ℝ
  have ha : a ≤ ‖u‖ + 4 := by
    dsimp [a]
    linarith [Real.sqrt_nonneg (1 + ‖perpendicular v u‖ ^ 2)]
  have htheta : theta a ≤ ‖u‖ + 4 :=
    (theta_le_positive a).trans (max_le ha (by positivity))
  have hsq : 10 * ‖u‖ - 50 * q ≤ ‖u‖ ^ 2 / (2 * q) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * q)).mpr
    nlinarith [sq_nonneg (‖u‖ - 10 * q)]
  change -91 * q ≤ Real.sqrt (1 + ‖u‖ ^ 2) - 1 + ‖u‖ ^ 2 / (2 * q) - 10 * theta a
  linarith [Real.sqrt_nonneg (1 + ‖u‖ ^ 2)]

noncomputable def previousGate {M : ℕ} (q : ℝ) (v u : Fin (M + 1) → E) (j : Fin (M + 1)) : ℝ :=
  if hj : j.val = 0 then 1 else
    exitGate q (v ⟨j.val - 1, by omega⟩) (u ⟨j.val - 1, by omega⟩)

theorem previousGate_zero {M : ℕ} {q : ℝ} (hq : 0 < q) (v : Fin (M + 1) → E)
    (j : Fin (M + 1)) : previousGate q v (fun _ => 0) j = if j = 0 then 1 else 0 := by
  unfold previousGate
  by_cases hj : j = 0
  · subst j
    simp
  · have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
    simp [hj, hjv, exitGate_zero hq]

/-- Literal Section D value expression, on `M+1 ≥ 1` stages. -/
noncomputable def value {M : ℕ} (q : ℝ) (v z u : Fin (M + 1) → E) : ℝ :=
  (∑ j, (clock q (v j) (z j) (u j) + guard 3000 (z j))) +
    Real.sqrt (∑ j, (previousGate q v u j) ^ 2 * ‖zeta (z j) - v j‖ ^ 2)

theorem value_zero {M : ℕ} {q : ℝ} (hq : 0 < q) (v : Fin (M + 1) → E)
    (hv : ∀ j, ‖v j‖ = 1) : value q v (fun _ => 0) (fun _ => 0) = 1 := by
  have hg0 : ConeRadial.guard 3000 (0 : E) = 0 := by
    unfold ConeRadial.guard
    rw [norm_zero]
    exact guardProfile_zero (by norm_num : (0 : ℝ) ≤ 3 / 2)
  unfold value
  simp only [clock_zero, hg0,
    add_zero, Finset.sum_const_zero, previousGate_zero hq, zeta_zero, zero_sub, norm_neg, hv]
  simp

theorem value_lower_bound {M : ℕ} {q : ℝ} (hq : 1 ≤ q) (v : Fin (M + 1) → E)
    (hv : ∀ j, ‖v j‖ = 1) (z u : Fin (M + 1) → E) :
    -91 * (M + 1 : ℕ) * q ≤ value q v z u := by
  have hl (j : Fin (M + 1)) : -91 * q ≤ clock q (v j) (z j) (u j) + guard 3000 (z j) := by
    have hh := clock_lower_bound hq (v j) (hv j) (z j) (u j)
    linarith [guard_nonneg (by norm_num : (0 : ℝ) ≤ 3000) (z j)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hl j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  unfold value
  linarith [Real.sqrt_nonneg (∑ j, (previousGate q v u j) ^ 2 * ‖zeta (z j) - v j‖ ^ 2)]

/-- The complete initial-gap conclusion of D admissibility for the explicit
value expression. The number of stages is `M+1`, so its source constant is
exactly `1+91*(M+1)*q`. -/
theorem value_initial_gap {M : ℕ} {q : ℝ} (hq : 1 ≤ q) (v : Fin (M + 1) → E)
    (hv : ∀ j, ‖v j‖ = 1) :
    value q v (fun _ => 0) (fun _ => 0) -
      sInf (Set.range (fun p : (Fin (M + 1) → E) × (Fin (M + 1) → E) => value q v p.1 p.2)) ≤
        1 + 91 * (M + 1 : ℕ) * q := by
  rw [value_zero (by linarith : 0 < q) v hv]
  have hl : -91 * (M + 1 : ℕ) * q ≤
      sInf (Set.range (fun p : (Fin (M + 1) → E) × (Fin (M + 1) → E) => value q v p.1 p.2)) := by
    apply le_csInf (Set.range_nonempty _)
    intro a ha
    obtain ⟨p, rfl⟩ := ha
    exact value_lower_bound hq v hv p.1 p.2
  linarith

end NCConcave16991.ConeClockGap
