import MatchingBounds1005.ChainQuadratic
import MatchingBounds1005.ChainGap
import MatchingBounds1005.BlockReadouts
import MatchingBounds1005.HorizonCalibration
import MatchingBounds1005.RadialComposition

/-! All-order derivative budgets for the actual chain and its radial composition. -/
noncomputable section
open scoped BigOperators InnerProductSpace ContDiff

namespace MatchingBounds1005.Primitive

theorem finite_order_bounds (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, 1 ≤ q → q ≤ p → ∀ r : ℝ, 1 ≤ r → ∀ u : ℝ,
      |iteratedDeriv (q + 1) (potential r) u| ≤ C * r ^ 3 / r ^ q := by
  induction p with
  | zero => exact ⟨0, le_rfl, fun q hq hqp => by omega⟩
  | succ p ih =>
    obtain ⟨C, hC, hc⟩ := ih
    obtain ⟨D, hD, hd⟩ := potential_derivative_bound (p + 1) (by omega)
    refine ⟨max C D, le_trans hC (le_max_left _ _), fun q hq hqp r hr u => ?_⟩
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    by_cases hqp' : q ≤ p
    · exact (hc q hq hqp' r hr u).trans (by gcongr; exact le_max_left _ _)
    · have heq : q = p + 1 := by omega
      subst q
      exact (hd r hr u).trans (by gcongr; exact le_max_right _ _)

end MatchingBounds1005.Primitive

namespace MatchingBounds1005.BlockGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (G : BlockGeometry E)

theorem euclideanObjective_eq_add (r : ℝ) (n : ℕ) :
    G.euclideanObjective r n = G.euclideanQuadratic n + G.euclideanPotential r n :=
  funext (fun z => G.euclideanObjective_decomposition r n z)

theorem euclideanObjective_smooth (r : ℝ) (n : ℕ) : ContDiff ℝ ∞ (G.euclideanObjective r n) := by
  rw [G.euclideanObjective_eq_add]
  exact (G.euclideanQuadratic_smooth n).add (G.euclideanPotential_smooth r n)

theorem euclideanObjective_jet_bound {A : ℝ} (hA : 0 < A) (ha : ‖G.a‖ = A)
    (r : ℝ) (n k : ℕ) {C Q : ℝ} (hC : 0 ≤ C) (hQ : 0 ≤ Q)
    (hb : ∀ u, |iteratedDeriv (k + 2) (Primitive.potential r) u| ≤ C)
    (hq : ∀ z, ‖iteratedFDeriv ℝ 2 (G.euclideanQuadratic n) z‖ ≤ Q)
    (z : BlockSpace (E := E) n) :
    ‖iteratedFDeriv ℝ (k + 2) (G.euclideanObjective r n) z‖ ≤ Q + G.tau * C * A ^ (k + 2) := by
  have hlevel : ((k + 2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
    generalize k + 2 = j
    exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)
  have hquad : ‖iteratedFDeriv ℝ (k + 2) (G.euclideanQuadratic n) z‖ ≤ Q := by
    rcases k with _ | k
    · exact hq z
    · have hz := congrFun (G.euclideanQuadratic_higher_zero n k) z
      change ‖iteratedFDeriv ℝ (k + 3) (G.euclideanQuadratic n) z‖ ≤ Q
      rw [hz]
      simpa only [Pi.zero_apply, norm_zero] using hQ
  have hpot := G.euclideanPotential_derivative_bound hA ha r n k hC hb z
  rw [abs_of_nonneg G.tau_nonneg] at hpot
  rw [G.euclideanObjective_eq_add, iteratedFDeriv_add_apply
    ((G.euclideanQuadratic_smooth n).of_le hlevel).contDiffAt
    ((G.euclideanPotential_smooth r n).of_le hlevel).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add hquad hpot)

theorem euclideanObjective_core_jet_bound {A : ℝ} (hA : 0 < A) (ha : ‖G.a‖ = A)
    (n k : ℕ) {C Q : ℝ} (hC : 0 ≤ C) (hQ : 0 ≤ Q)
    (hb : ∀ u, |iteratedDeriv (k + 2) (Primitive.potential A) u| ≤ C * A ^ 3 / A ^ (k + 1))
    (hq : ∀ z, ‖iteratedFDeriv ℝ 2 (G.euclideanQuadratic n) z‖ ≤ Q)
    (z : BlockSpace (E := E) n) :
    ‖iteratedFDeriv ℝ (k + 2) (G.euclideanObjective A n) z‖ ≤ Q + C * (G.tau * A ^ 4) := by
  have hbnd := G.euclideanObjective_jet_bound hA ha A n k (by positivity) hQ hb hq z
  convert hbnd using 1
  congr 1
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  field_simp
  ring

theorem euclideanGradient_zero (r : ℝ) (n : ℕ) :
    G.euclideanGradient r n 0 =
      (WithLp.equiv 2 (Fin (n + 1) → E)).symm (Pi.single 0 (-G.lam • G.e)) := by
  ext i
  change G.gradientBlock (Primitive.slope r) (G.incomingReadout 0 i) 0 (G.outgoingEntry 0 i) = _
  by_cases hi : i = 0
  · subst i
    simp [gradientBlock, incomingReadout, outgoingEntry, Primitive.slope]
  · simp [gradientBlock, incomingReadout, outgoingEntry, Primitive.slope, hi, Pi.single_eq_of_ne hi]

theorem euclideanObjective_first_jet_zero (r : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ 1 (G.euclideanObjective r n) 0‖ = G.lam * ‖G.e‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero,
    (G.euclideanObjective_hasFDerivAt r n 0).fderiv, innerSL_apply_norm,
    G.euclideanGradient_zero, PiLp.norm_equiv_symm_single, norm_smul,
    Real.norm_eq_abs, abs_neg, abs_of_nonneg G.lam_nonneg]

theorem euclideanObjective_radial_budget (r : ℝ) (n j : ℕ) (hj : 2 ≤ j)
    {R b : ℝ} (hR : 0 < R) (hb : 0 ≤ b)
    (hjet : ∀ q, 2 ≤ q → q ≤ j → ∀ z : BlockSpace (E := E) n,
      ‖iteratedFDeriv ℝ q (G.euclideanObjective r n) z‖ ≤ b)
    (x : BlockSpace (E := E) n) :
    ‖iteratedFDeriv ℝ j (G.euclideanObjective r n ∘ radial R) x‖ ≤
      2 * RadialHigher.compositionConstant j *
        (G.lam * ‖G.e‖ * R + ∑ q ∈ Finset.Icc 2 j, b * R ^ q) / R ^ j := by
  have hlevel : (j : WithTop ℕ∞) ≤ ∞ :=
    by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)
  have h := RadialHigher.radial_composition_budget hj
    ((G.euclideanObjective_smooth r n).of_le hlevel) hR (fun _ => b)
    (fun _ _ _ => hb) hjet x
  rwa [G.euclideanObjective_first_jet_zero] at h

end MatchingBounds1005.BlockGeometry

namespace MatchingBounds1005.EpsilonCalibration
open PathGreen
variable (a L t : ℝ) (ha : 0 < a) (hL : 0 < L) (ht : 0 < t)
  (hhsmall : pathScale a L t ≤ 1 / 4)
local notation "G" => geometry a L t ha hL ht hhsmall

theorem calibrated_jet_bound (p : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hprim : ∀ q, 1 ≤ q → q ≤ p → ∀ r, 1 ≤ r → ∀ u,
      |iteratedDeriv (q + 1) (Primitive.potential r) u| ≤ C * r ^ 3 / r ^ q)
    (hbudget : 18 * 8192 * C * a ^ 3 ≤ 4 * L)
    (hr : t ≤ a) (hpath : pathScale a L t ≤ 1 / 37)
    (q : ℕ) (hq : 1 ≤ q) (hqp : q ≤ p) (n : ℕ)
    (z : BlockGeometry.BlockSpace (E := EuclideanSpace ℝ (Fin (pathEdges (pathScale a L t) + 1))) n) :
    ‖iteratedFDeriv ℝ (q + 1) ((G).euclideanObjective (amplitude a t) n) z‖ ≤ 16 * L := by
  have hA := amplitude_pos a t ha ht
  have hnorm : ‖(G).a‖ = amplitude a t :=
    suffixVector_norm (amplitude a t) hA.le _
  have hQ : ∀ y, ‖iteratedFDeriv ℝ 2 ((G).euclideanQuadratic n) y‖ ≤ 8 * L := by
    intro y
    exact (actual_quadratic_second_bound L (pathScale a L t) (amplitude a t) hL
      (pathScale_pos a L t ha hL ht) hhsmall hA n y).trans
      (quadratic_coefficient_small L (pathScale a L t) hL
        (pathScale_pos a L t ha hL ht) hpath)
  have hqeq : q - 1 + 2 = q + 1 := by omega
  have hcore := (G).euclideanObjective_core_jet_bound hA hnorm n (q - 1) hC (by positivity)
    (by simpa only [hqeq, Nat.sub_add_cancel hq] using
      hprim q hq hqp (amplitude a t) (amplitude_ge_one a t ht hr)) hQ z
  rw [hqeq] at hcore
  have hnonlinear := mul_le_mul_of_nonneg_left
    (calibrated_nonlinear_budget a L t ha hL ht hhsmall) hC
  nlinarith only [hcore, hnonlinear, hbudget, hL]

theorem calibrated_actual_gap (hr : t ≤ a) (hphase : 1 ≤ phaseCount a t)
    (hsmall : 10368 * 8192 * t ^ 4 ≤ a)
    (z : BlockGeometry.BlockSpace
      (E := EuclideanSpace ℝ (Fin (pathEdges (pathScale a L t) + 1))) (phaseCount a t - 1)) :
    (G).euclideanObjective (amplitude a t) (phaseCount a t - 1) 0 -
      (G).euclideanObjective (amplitude a t) (phaseCount a t - 1) z ≤ 1 / 4 := by
  have h := (G).euclideanObjective_gap (amplitude a t) (amplitude_ge_one a t ht hr)
    (phaseCount a t - 1) z
  conv at h => rhs; rw [Nat.sub_add_cancel hphase]
  exact h.trans (calibrated_gap a L t ha hL ht hhsmall hsmall)

end MatchingBounds1005.EpsilonCalibration
