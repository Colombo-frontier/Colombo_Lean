import LeanArticleAudit.Pilot.UpperInterfaces

/-!
# Finite acceleration hierarchy

This file isolates the exact exponent and logarithmic-power arithmetic used
in the final upper-bound induction.  The algorithmic transformations are
proved in `UpperRestart` and `UpperBoost`.
-/

namespace LeanArticleAudit.Pilot

noncomputable section

/-- Residual exponent after `j` acceleration levels. -/
def hierarchyGamma (p j : ℕ) : ℝ := 2 / (p + 1 + 2 * j : ℝ)

/-- Logarithmic power of the residual solver at level `j`. -/
def hierarchyResidualLogPower (j : ℕ) : ℕ := 6 * j

/-- Logarithmic power after restarting residual level `j`. -/
def hierarchyStrongLogPower (j : ℕ) : ℕ := 6 * j + 2

theorem hierarchyGamma_zero (p : ℕ) :
    hierarchyGamma p 0 = 2 / (p + 1 : ℝ) := by
  simp [hierarchyGamma]

theorem hierarchyGamma_succ (p j : ℕ) :
    hierarchyGamma p (j + 1) =
      hierarchyGamma p j / (1 + hierarchyGamma p j) := by
  rw [hierarchyGamma, hierarchyGamma]
  push_cast
  have hden : (p : ℝ) + 1 + 2 * (j : ℝ) ≠ 0 := by positivity
  field_simp [hden]
  ring

theorem hierarchy_log_power_boost (j : ℕ) :
    hierarchyStrongLogPower j + 4 = hierarchyResidualLogPower (j + 1) := by
  simp [hierarchyStrongLogPower, hierarchyResidualLogPower]
  omega

theorem hierarchy_log_power_restart (j : ℕ) :
    hierarchyResidualLogPower j + 2 = hierarchyStrongLogPower j := by
  simp [hierarchyStrongLogPower, hierarchyResidualLogPower]

theorem hierarchyGamma_pos {p j : ℕ} : 0 < hierarchyGamma p j := by
  rw [hierarchyGamma]
  positivity

/-- Every one of the `p-1` boost calls lies in the proved power-mean range. -/
theorem hierarchy_boost_range {p i : ℕ} (hp : 2 ≤ p) (hi : i ≤ p - 2) :
    (p - 1 : ℝ) * hierarchyGamma p i ≤ 2 ∧
    1 ≤ (3 / 2 : ℝ) * ((p - 1 : ℝ) * hierarchyGamma p i) := by
  have hp1 : 1 ≤ p := by omega
  have hpR : 0 < (p + 1 + 2 * i : ℝ) := by positivity
  have hsub : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp1]
    norm_num
  have hiNat : 2 * i ≤ 2 * (p - 2) := Nat.mul_le_mul_left 2 hi
  have hiR : (2 * i : ℝ) ≤ 2 * (p - 2 : ℝ) := by exact_mod_cast hiNat
  have hp2 : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
    rw [Nat.cast_sub hp]
    norm_num
  rw [hierarchyGamma]
  constructor
  · rw [show ((p : ℝ) - 1) * (2 / ((p : ℝ) + 1 + 2 * (i : ℝ))) =
        2 * ((p : ℝ) - 1) / ((p : ℝ) + 1 + 2 * (i : ℝ)) by ring]
    apply (div_le_iff₀ hpR).2
    nlinarith
  · rw [show (3 / 2 : ℝ) * (((p : ℝ) - 1) *
        (2 / ((p : ℝ) + 1 + 2 * (i : ℝ)))) =
        3 * ((p : ℝ) - 1) / ((p : ℝ) + 1 + 2 * (i : ℝ)) by ring]
    apply (le_div_iff₀ hpR).2
    nlinarith

/-- After exactly `p-1` levels the exponent is the matching one. -/
theorem hierarchyGamma_final {p : ℕ} (hp : 1 ≤ p) :
    hierarchyGamma p (p - 1) = 2 / (3 * p - 1 : ℝ) := by
  rw [hierarchyGamma]
  rw [Nat.cast_sub hp]
  push_cast
  congr 1
  ring

theorem hierarchyResidualLogPower_final {p : ℕ} :
    hierarchyResidualLogPower (p - 1) = 6 * (p - 1) := rfl

section DiameterSubstitution

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- With the valid universal radius `R=D`, the distance-sensitive logarithm
is literally the one displayed in `thm:main`. -/
theorem residualLog_at_diameter (data : VIPublicData E) (epsilon : ℝ) :
    residualLog data data.D epsilon =
      1 + Real.log (3 + residualCondition data data.D epsilon) := by
  rw [residualLog]
  have hD0 : data.D ≠ 0 := ne_of_gt data.D_pos
  rw [div_self hD0]
  congr 2
  ring

/-- The corresponding interface cost has no dimension parameter. -/
theorem residualInterfaceCost_at_diameter
    (data : VIPublicData E) (C alpha : ℝ) (b : ℕ) (epsilon : ℝ) :
    residualInterfaceCost data C alpha b data.D epsilon =
      C * (1 + (data.Lp * data.D ^ data.p / epsilon) ^ alpha) *
        (1 + Real.log (3 + data.Lp * data.D ^ data.p / epsilon)) ^ b := by
  rw [residualInterfaceCost, residualLog_at_diameter, residualCondition]

end DiameterSubstitution

section FiniteConstruction

/-- Existence of a residual implementation with its full executable
interface, specialized to ordinary finite-dimensional real spaces. -/
def HasResidualSolver (p : ℕ) (alpha : ℝ) (b : ℕ) : Prop :=
  ∃ A : ResidualSolverFamily.{0} p, A.SatisfiesInterface alpha b

/-- Existence of the corresponding strong implementation. -/
def HasStrongSolver (p : ℕ) (gamma : ℝ) (b : ℕ) : Prop :=
  ∃ S : StrongSolverFamily.{0} p, S.SatisfiesInterface gamma b

/-- Pure finite induction behind the final hierarchy.  Each level consumes
only the solver constructed at the immediately preceding level; there is no
self-call to an unknown optimal method. -/
theorem finite_upper_hierarchy
    (p : ℕ) (hp : 2 ≤ p)
    (hbase : HasStrongSolver p (hierarchyGamma p 0)
      (hierarchyStrongLogPower 0))
    (hboost : ∀ i, i ≤ p - 2 →
      HasStrongSolver p (hierarchyGamma p i) (hierarchyStrongLogPower i) →
      HasResidualSolver p (hierarchyGamma p (i + 1))
        (hierarchyResidualLogPower (i + 1)))
    (hrestart : ∀ j, 1 ≤ j → j ≤ p - 2 →
      HasResidualSolver p (hierarchyGamma p j) (hierarchyResidualLogPower j) →
      HasStrongSolver p (hierarchyGamma p j) (hierarchyStrongLogPower j)) :
    HasResidualSolver p (2 / (3 * p - 1 : ℝ)) (6 * (p - 1)) := by
  have hstrong : ∀ j, j ≤ p - 2 →
      HasStrongSolver p (hierarchyGamma p j) (hierarchyStrongLogPower j) := by
    intro j hj
    induction j with
    | zero => exact hbase
    | succ j ih =>
        have hj' : j ≤ p - 2 := by omega
        exact hrestart (j + 1) (by omega) hj
          (hboost j hj' (ih hj'))
  have hlastStrong := hstrong (p - 2) le_rfl
  have hlastResidual := hboost (p - 2) le_rfl hlastStrong
  have hidx : p - 2 + 1 = p - 1 := by omega
  rw [hidx, hierarchyGamma_final (by omega : 1 ≤ p),
    hierarchyResidualLogPower_final] at hlastResidual
  exact hlastResidual

end FiniteConstruction

/-- Exact finite arithmetic bundle used by `thm:main`. -/
def UpperHierarchyArithmeticClaim : Prop :=
  ∀ p, 2 ≤ p →
    hierarchyGamma p 0 = 2 / (p + 1 : ℝ) ∧
    (∀ j, hierarchyGamma p (j + 1) =
      hierarchyGamma p j / (1 + hierarchyGamma p j)) ∧
    (∀ i, i ≤ p - 2 →
      (p - 1 : ℝ) * hierarchyGamma p i ≤ 2 ∧
      1 ≤ (3 / 2 : ℝ) * ((p - 1 : ℝ) * hierarchyGamma p i)) ∧
    hierarchyGamma p (p - 1) = 2 / (3 * p - 1 : ℝ) ∧
    hierarchyResidualLogPower (p - 1) = 6 * (p - 1)

theorem upperHierarchyArithmeticClaim_proof : UpperHierarchyArithmeticClaim := by
  intro p hp
  exact ⟨hierarchyGamma_zero p, hierarchyGamma_succ p,
    fun i hi => hierarchy_boost_range hp hi,
    hierarchyGamma_final (by omega), hierarchyResidualLogPower_final⟩

end

end LeanArticleAudit.Pilot
