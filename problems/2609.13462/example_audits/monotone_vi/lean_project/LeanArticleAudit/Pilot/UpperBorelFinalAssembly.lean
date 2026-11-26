import LeanArticleAudit.Pilot.UpperBorelBase
import LeanArticleAudit.Pilot.UpperBorelBoostRestart
import LeanArticleAudit.Pilot.UpperBorelHierarchy
import LeanArticleAudit.Pilot.UpperBorelRestart
import LeanArticleAudit.Pilot.UpperFinalAssembly

/-!
# Final capped-Borel upper assembly

This module separates the scalar arithmetic of the finite hierarchy from the
concrete Borel-preservation proofs for base, boost, and restart.  The latter
are stated on the actual locally capped, anchor-uniform call observable, so no
pointwise or uncapped measurability premise is silently strengthened here.
-/

namespace LeanArticleAudit.Pilot

noncomputable section

/-- Install the certified base family at hierarchy level zero once its actual
capped calls have the anchor-uniform Borel outcome property. -/
theorem hierarchy_base_hasJointBorel_of_capped
    (p : ℕ)
    (hBorel : (baseStrongCertifiedFamily p : StrongSolverFamily.{0} p)
      |>.HasJointBorelCappedOutcome) :
    HasJointBorelStrongSolver p (hierarchyGamma p 0)
      (hierarchyStrongLogPower 0) := by
  refine ⟨(baseStrongCertifiedFamily p : StrongSolverFamily.{0} p), ?_, hBorel⟩
  simpa [hierarchyGamma_zero, hierarchyStrongLogPower] using
    prop_base_strong p

/-- The numerical boost edge, retaining the honest capped/anchored Borel
invariant supplied by the concrete program-preservation theorem. -/
theorem hierarchy_boost_hasJointBorel_of_preservation
    (preservesBoost : ∀ (p : ℕ) (S : StrongSolverFamily.{0} p)
      (gamma : ℝ) (b : ℕ),
      S.HasJointBorelCappedOutcome →
        (boostedResidualFamily p S gamma b).HasJointBorelCappedOutcome)
    (p : ℕ) (hp : 2 ≤ p) (i : ℕ) (hi : i ≤ p - 2)
    (hstrong : HasJointBorelStrongSolver p (hierarchyGamma p i)
      (hierarchyStrongLogPower i)) :
    HasJointBorelResidualSolver p (hierarchyGamma p (i + 1))
      (hierarchyResidualLogPower (i + 1)) := by
  obtain ⟨S, hS, hSBorel⟩ := hstrong
  have hrange := hierarchy_boost_range hp hi
  have hgamma1 : hierarchyGamma p i ≤ 1 := by
    unfold hierarchyGamma
    apply (div_le_one (by positivity : (0 : ℝ) < p + 1 + 2 * i)).2
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
    push_cast
    linarith
  have hsub : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    norm_num
  have ha23 : 2 / 3 ≤ ((p - 1 : ℕ) : ℝ) * hierarchyGamma p i := by
    rw [hsub]
    linarith [hrange.2]
  have ha2 : ((p - 1 : ℕ) : ℝ) * hierarchyGamma p i ≤ 2 := by
    rw [hsub]
    exact hrange.1
  refine ⟨boostedResidualFamily p S (hierarchyGamma p i)
      (hierarchyStrongLogPower i), ?_, ?_⟩
  · rw [hierarchyGamma_succ, ← hierarchy_log_power_boost]
    exact boostedResidualFamily_satisfies p S (hierarchyGamma p i)
      (hierarchyStrongLogPower i) hS hierarchyGamma_pos hgamma1 ha23 ha2
  · exact preservesBoost p S (hierarchyGamma p i)
      (hierarchyStrongLogPower i) hSBorel

/-- The numerical certified-restart edge, retaining the actual capped and
anchor-uniform Borel observable supplied by its preservation theorem. -/
theorem hierarchy_restart_hasJointBorel_of_preservation
    (preservesRestart : ∀ (p : ℕ) (A : ResidualSolverFamily.{0} p)
      (alpha : ℝ) (b : ℕ),
      A.HasJointBorelCappedOutcome →
        (certifiedRestartFamily p A alpha b).HasJointBorelCappedOutcome)
    (p : ℕ) (hp : 2 ≤ p) (j : ℕ)
    (_hj0 : 1 ≤ j) (_hjp : j ≤ p - 2)
    (hresidual : HasJointBorelResidualSolver p (hierarchyGamma p j)
      (hierarchyResidualLogPower j)) :
    HasJointBorelStrongSolver p (hierarchyGamma p j)
      (hierarchyStrongLogPower j) := by
  obtain ⟨A, hA, hABorel⟩ := hresidual
  have hgamma0 : 0 < hierarchyGamma p j := hierarchyGamma_pos
  have hgamma1 : hierarchyGamma p j ≤ 1 := by
    unfold hierarchyGamma
    apply (div_le_one (by positivity : (0 : ℝ) < p + 1 + 2 * j)).2
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
    push_cast
    linarith
  refine ⟨certifiedRestartFamily p A (hierarchyGamma p j)
      (hierarchyResidualLogPower j), ?_, ?_⟩
  · simpa [hierarchyStrongLogPower, hierarchyResidualLogPower] using
      certifiedRestartFamily_satisfies p A (hierarchyGamma p j)
        (hierarchyResidualLogPower j) hA hgamma0 hgamma1
  · exact preservesRestart p A (hierarchyGamma p j)
      (hierarchyResidualLogPower j) hABorel

/-- Final finite-hierarchy result reduced exactly to the three concrete
capped/anchored preservation facts. -/
theorem final_upper_joint_borel_hierarchy_of_preservation
    (baseBorel : ∀ p,
      (baseStrongCertifiedFamily p : StrongSolverFamily.{0} p)
        |>.HasJointBorelCappedOutcome)
    (preservesBoost : ∀ (p : ℕ) (S : StrongSolverFamily.{0} p)
      (gamma : ℝ) (b : ℕ),
      S.HasJointBorelCappedOutcome →
        (boostedResidualFamily p S gamma b).HasJointBorelCappedOutcome)
    (preservesRestart : ∀ (p : ℕ) (A : ResidualSolverFamily.{0} p)
      (alpha : ℝ) (b : ℕ),
      A.HasJointBorelCappedOutcome →
        (certifiedRestartFamily p A alpha b).HasJointBorelCappedOutcome)
    (p : ℕ) (hp : 2 ≤ p) :
    HasJointBorelResidualSolver p (2 / (3 * p - 1 : ℝ))
      (6 * (p - 1)) := by
  exact finite_upper_joint_borel_hierarchy p hp
    (hierarchy_base_hasJointBorel_of_capped p (baseBorel p))
    (hierarchy_boost_hasJointBorel_of_preservation preservesBoost p hp)
    (hierarchy_restart_hasJointBorel_of_preservation preservesRestart p hp)

/-- The concrete final residual family produced by the finite hierarchy has
jointly Borel full outcomes for its actual capped calls, uniformly in the
shifted anchor.  No measurability premise is left to the client. -/
theorem final_upper_joint_borel_hierarchy
    (p : ℕ) (hp : 2 ≤ p) :
    HasJointBorelResidualSolver p (2 / (3 * p - 1 : ℝ))
      (6 * (p - 1)) := by
  exact final_upper_joint_borel_hierarchy_of_preservation
    (fun q => baseStrongCertifiedFamily_hasJointBorelCappedOutcome q)
    (fun q S gamma b hS =>
      boostedResidualFamily_hasJointBorelCappedOutcome q S hS gamma b)
    (fun q A alpha b hA =>
      certifiedRestartFamily_hasJointBorelCappedOutcome A hA alpha b)
    p hp

end

end LeanArticleAudit.Pilot
