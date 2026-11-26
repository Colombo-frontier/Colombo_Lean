import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Scalar transition certificate (conditional on the potential estimates)

This proves the finite-chain argument in `ana:lem:scalar` of 1005 (2).tex.
The analytic construction of the smooth cutoff potential is NOT assumed proved:
the three estimates on its derivative are explicit hypotheses.  The conclusion
is stronger than the squared Euclidean norm bound required by that lemma.
-/

namespace MatchingBounds1005

def scalarResidual (ψ : ℝ → ℝ) (u : ℕ → ℝ) (i : ℕ) : ℝ :=
  2 * u i - u (i - 1) - u (i + 1) + ψ (u i)

def quarticCore (x : ℝ) : ℝ := 30 * x ^ 4 - 40 * x ^ 3 + 10

def quarticCoreDerivative (x : ℝ) : ℝ := 120 * x ^ 2 * (x - 1)

theorem quarticCore_nonneg (x : ℝ) : 0 ≤ quarticCore x := by
  have h : 0 ≤ 2 * x ^ 2 + (x + 1) ^ 2 := by positivity
  have := mul_nonneg (sq_nonneg (x - 1)) h
  unfold quarticCore
  nlinarith

/-- The radial constant in `ana:eq:radial-primitive`, for the exact core. -/
theorem quarticCore_radial (x : ℝ) :
    -(405 / 32 : ℝ) ≤ x * quarticCoreDerivative x := by
  have h : 0 ≤ (4 * x + 1) ^ 2 + 2 := by positivity
  have := mul_nonneg (sq_nonneg (4 * x - 3)) h
  unfold quarticCoreDerivative
  nlinarith

theorem quarticCoreDerivative_nonpos (x : ℝ) (hx : x < 1) :
    quarticCoreDerivative x ≤ 0 := by
  unfold quarticCoreDerivative
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)

theorem quarticCoreDerivative_negative_tail (x : ℝ) (hx : x ≤ -(1 / 10 : ℝ)) :
    quarticCoreDerivative x ≤ -(33 / 25 : ℝ) := by
  have hx2 : (1 / 100 : ℝ) ≤ x ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hx2 (show 0 ≤ 1 - x by linarith)
  unfold quarticCoreDerivative
  nlinarith

/-- The nonsingular algebraic expression for the article's tapered derivative.
It agrees with `120*x^2*(x-1)*W(x/r)` for its cutoff-defined `W`. This file does
not prove the fundamental theorem of calculus identification with `φ_r'`. -/
noncomputable def taperedDerivative (r : ℝ) (χ : ℝ → ℝ) (x : ℝ) : ℝ :=
  120 * (χ (x / r) * x ^ 2 + (1 - χ (x / r)) * r ^ 2) * (x - 1)

theorem taperedDerivative_nonpos (r : ℝ) (χ : ℝ → ℝ)
    (hχ : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1) (x : ℝ) (hx : x < 1) :
    taperedDerivative r χ x ≤ 0 := by
  rcases hχ (x / r) with ⟨hc0, hc1⟩
  have hc2 : 0 ≤ 1 - χ (x / r) := sub_nonneg.mpr hc1
  unfold taperedDerivative
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)

theorem taperedDerivative_negative_tail (r : ℝ) (hr : 1 ≤ r) (χ : ℝ → ℝ)
    (hχ : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1) (x : ℝ) (hx : x ≤ -(1 / 10 : ℝ)) :
    taperedDerivative r χ x ≤ -(33 / 25 : ℝ) := by
  have hx2 : (1 / 100 : ℝ) ≤ x ^ 2 := by nlinarith
  have hr2 : (1 / 100 : ℝ) ≤ r ^ 2 := by nlinarith
  have hc := hχ (x / r)
  have hleft := mul_le_mul_of_nonneg_left hx2 hc.1
  have hright := mul_le_mul_of_nonneg_left hr2 (sub_nonneg.mpr hc.2)
  have hmix : (1 / 100 : ℝ) ≤ χ (x / r) * x ^ 2 + (1 - χ (x / r)) * r ^ 2 := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hmix (show 0 ≤ 1 - x by linarith)
  unfold taperedDerivative
  nlinarith

theorem taperedDerivative_core (r : ℝ) (hr : 1 ≤ r) (χ : ℝ → ℝ)
    (hχcore : ∀ t, |t| ≤ 1 → χ t = 1)
    (x : ℝ) (hlo : (1 / 10 : ℝ) ≤ x) (hhi : x ≤ (9 / 10 : ℝ)) :
    taperedDerivative r χ x = 120 * x ^ 2 * (x - 1) := by
  have hrpos : 0 < r := by linarith
  have hxpos : 0 ≤ x := by linarith
  have hdiv : |x / r| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg hxpos hrpos.le)]
    exact (div_le_one hrpos).mpr (by linarith)
  simp [taperedDerivative, hχcore (x / r) hdiv]

theorem taperedDerivative_exact_core (r : ℝ) (hr : 0 < r) (χ : ℝ → ℝ)
    (hχcore : ∀ t, |t| ≤ 1 → χ t = 1)
    (x : ℝ) (hx : |x| ≤ r) :
    taperedDerivative r χ x = quarticCoreDerivative x := by
  have hdiv : |x / r| ≤ 1 := by
    rw [abs_div, abs_of_pos hr]
    exact (div_le_one hr).mpr hx
  simp [taperedDerivative, quarticCoreDerivative, hχcore (x / r) hdiv]

/-- Global radial bound for every allowed cutoff; no smoothness is needed. -/
theorem taperedDerivative_radial (r : ℝ) (hr : 1 ≤ r) (χ : ℝ → ℝ)
    (hχ : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1)
    (hχcore : ∀ t, |t| ≤ 1 → χ t = 1) (x : ℝ) :
    -(405 / 32 : ℝ) ≤ x * taperedDerivative r χ x := by
  rcases hχ (x / r) with ⟨hc0, hc1⟩
  have hc2 : 0 ≤ 1 - χ (x / r) := sub_nonneg.mpr hc1
  have hmix : 0 ≤ 120 * (χ (x / r) * x ^ 2 + (1 - χ (x / r)) * r ^ 2) := by
    positivity
  by_cases hlo : x ≤ 0
  · have hmul : 0 ≤ x * (x - 1) := mul_nonneg_of_nonpos_of_nonpos hlo (by linarith)
    have hh := mul_nonneg hmix hmul
    unfold taperedDerivative
    nlinarith
  by_cases hhi : 1 ≤ x
  · have hmul : 0 ≤ x * (x - 1) := mul_nonneg (by linarith) (by linarith)
    have hh := mul_nonneg hmix hmul
    unfold taperedDerivative
    nlinarith
  have hxabs : |x| ≤ r := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  rw [taperedDerivative_exact_core r (by linarith) χ hχcore x hxabs]
  exact quarticCore_radial x

/-- The scalar transition argument, with all needed potential facts explicit. -/
theorem scalar_transition_coordinate
    (ψ : ℝ → ℝ)
    (hneg : ∀ x : ℝ, x ≤ -(1 / 10 : ℝ) → ψ x ≤ -(33 / 25 : ℝ))
    (hcore : ∀ x : ℝ, (1 / 10 : ℝ) ≤ x → x ≤ (9 / 10 : ℝ) →
      ψ x = 120 * x ^ 2 * (x - 1))
    (hnonpos : ∀ x : ℝ, x < 1 → ψ x ≤ 0)
    (N : ℕ) (_hN : 1 ≤ N) (u : ℕ → ℝ)
    (hu0 : u 0 = 1) (huend : u (N + 1) = 0)
    (huN : u N < (1 / 10 : ℝ)) :
    ∃ i ∈ Finset.Icc 1 N, (1 / 4 : ℝ) ≤ |scalarResidual ψ u i| := by
  classical
  by_contra! hsmall
  have hres (i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) :
      -(1 / 4 : ℝ) < scalarResidual ψ u i := by
    exact (abs_lt.mp (hsmall i (Finset.mem_Icc.mpr ⟨hi, hiN⟩))).1
  have hrange : (Finset.range (N + 2)).Nonempty := ⟨0, by simp⟩
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (Finset.range (N + 2)) u hrange
  have hmN : m ≤ N + 1 := by
    have := Finset.mem_range.mp hm
    omega
  have hminlower : -(1 / 10 : ℝ) < u m := by
    by_contra hh
    have hmneg : u m ≤ -(1 / 10 : ℝ) := le_of_not_gt hh
    have hm0 : m ≠ 0 := by
      intro heq
      rw [heq, hu0] at hmneg
      norm_num at hmneg
    have hmend : m ≠ N + 1 := by
      intro heq
      rw [heq, huend] at hmneg
      norm_num at hmneg
    have hmpos : 1 ≤ m := by omega
    have hminN : m ≤ N := by omega
    have hprev : u m ≤ u (m - 1) := hmin _ (Finset.mem_range.mpr (by omega))
    have hnext : u m ≤ u (m + 1) := hmin _ (Finset.mem_range.mpr (by omega))
    have hp := hneg (u m) hmneg
    have hd := hres m hmpos hminN
    unfold scalarResidual at hd
    linarith
  have hlower (i : ℕ) (hi : i ≤ N + 1) : -(1 / 10 : ℝ) < u i :=
    lt_of_lt_of_le hminlower (hmin _ (Finset.mem_range.mpr (by omega)))
  have hno_middle (i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N)
      (hlo : (1 / 10 : ℝ) ≤ u i) : (9 / 10 : ℝ) < u i := by
    by_contra hh
    have hhi : u i ≤ (9 / 10 : ℝ) := le_of_not_gt hh
    have hprod : (9 / 100 : ℝ) ≤ u i * (1 - u i) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)]
    have huipos : 0 ≤ u i := by linarith
    have hprod2 := mul_le_mul_of_nonneg_left hprod huipos
    have hp := hcore (u i) hlo hhi
    have hprev := hlower (i - 1) (by omega)
    have hnext := hlower (i + 1) (by omega)
    have hd := hres i hi hiN
    unfold scalarResidual at hd
    rw [hp] at hd
    nlinarith
  have hex : ∃ j : ℕ, u j < (1 / 10 : ℝ) := ⟨N, huN⟩
  let j := Nat.find hex
  have hjlow : u j < (1 / 10 : ℝ) := Nat.find_spec hex
  have hjN : j ≤ N := Nat.find_min' hex huN
  have hj0 : j ≠ 0 := by
    intro hj
    rw [hj, hu0] at hjlow
    norm_num at hjlow
  have hjpos : 1 ≤ j := by omega
  have hprevlo : (1 / 10 : ℝ) ≤ u (j - 1) := by
    exact le_of_not_gt (Nat.find_min hex (by omega))
  have hprevhi : (9 / 10 : ℝ) < u (j - 1) := by
    by_cases hj1 : j = 1
    · norm_num [hj1, hu0]
    · exact hno_middle (j - 1) (by omega) (by omega) hprevlo
  have hnext := hlower (j + 1) (by omega)
  have hp := hnonpos (u j) (by linarith)
  have hd := hres j hjpos hjN
  unfold scalarResidual at hd
  linarith

/-- Squared Euclidean norm form of the scalar transition certificate. -/
theorem scalar_transition_squared
    (ψ : ℝ → ℝ)
    (hneg : ∀ x : ℝ, x ≤ -(1 / 10 : ℝ) → ψ x ≤ -(33 / 25 : ℝ))
    (hcore : ∀ x : ℝ, (1 / 10 : ℝ) ≤ x → x ≤ (9 / 10 : ℝ) →
      ψ x = 120 * x ^ 2 * (x - 1))
    (hnonpos : ∀ x : ℝ, x < 1 → ψ x ≤ 0)
    (N : ℕ) (hN : 1 ≤ N) (u : ℕ → ℝ)
    (hu0 : u 0 = 1) (huend : u (N + 1) = 0)
    (huN : u N < (1 / 10 : ℝ)) :
    (1 / 16 : ℝ) ≤ ∑ i ∈ Finset.Icc 1 N, scalarResidual ψ u i ^ 2 := by
  obtain ⟨i, hi, hbound⟩ :=
    scalar_transition_coordinate ψ hneg hcore hnonpos N hN u hu0 huend huN
  have hsquare : (1 / 16 : ℝ) ≤ scalarResidual ψ u i ^ 2 := by
    nlinarith [sq_abs (scalarResidual ψ u i)]
  exact hsquare.trans (Finset.single_le_sum (fun j _ => sq_nonneg (scalarResidual ψ u j)) hi)

/-- A fully instantiated polynomial-chain certificate. The article uses the
smooth tapered extension instead; its three derivative estimates still have
to be connected to `scalar_transition_squared`. -/
theorem quartic_scalar_transition_squared
    (N : ℕ) (hN : 1 ≤ N) (u : ℕ → ℝ)
    (hu0 : u 0 = 1) (huend : u (N + 1) = 0)
    (huN : u N < (1 / 10 : ℝ)) :
    (1 / 16 : ℝ) ≤ ∑ i ∈ Finset.Icc 1 N,
      scalarResidual quarticCoreDerivative u i ^ 2 :=
  scalar_transition_squared quarticCoreDerivative
    quarticCoreDerivative_negative_tail (fun _ _ _ => rfl)
    quarticCoreDerivative_nonpos N hN u hu0 huend huN

/-- The scalar transition for the article's actual tapered derivative profile.
Only the elementary cutoff range/core conditions are required. Smoothness and
identification as the derivative of the integral potential are separate. -/
theorem tapered_scalar_transition_squared
    (r : ℝ) (hr : 1 ≤ r) (χ : ℝ → ℝ)
    (hχ : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1)
    (hχcore : ∀ t, |t| ≤ 1 → χ t = 1)
    (N : ℕ) (hN : 1 ≤ N) (u : ℕ → ℝ)
    (hu0 : u 0 = 1) (huend : u (N + 1) = 0)
    (huN : u N < (1 / 10 : ℝ)) :
    (1 / 16 : ℝ) ≤ ∑ i ∈ Finset.Icc 1 N,
      scalarResidual (taperedDerivative r χ) u i ^ 2 :=
  scalar_transition_squared (taperedDerivative r χ)
    (taperedDerivative_negative_tail r hr χ hχ)
    (taperedDerivative_core r hr χ hχcore)
    (taperedDerivative_nonpos r χ hχ) N hN u hu0 huend huN

end MatchingBounds1005
