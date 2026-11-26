import VIReference.Pilot.UpperBaseStrongClaim
import VIReference.Pilot.UpperBoostTransformation
import VIReference.Pilot.UpperRestartClaim
import VIReference.Pilot.MainAssembly

namespace VIReference.Pilot

noncomputable section

/-- The certified base solver supplies level zero of the finite hierarchy. -/
theorem hierarchy_base_hasStrong (p : ℕ) :
    HasStrongSolver p (hierarchyGamma p 0) (hierarchyStrongLogPower 0) := by
  refine ⟨baseStrongCertifiedFamily p, ?_⟩
  simpa [hierarchyGamma_zero, hierarchyStrongLogPower] using prop_base_strong p

/-- The completed executable boost supplies every forward edge of the finite
hierarchy, including the endpoint edge when `p=2`. -/
theorem hierarchy_boost_hasResidual (p : ℕ) (hp : 2 ≤ p) (i : ℕ)
    (hi : i ≤ p - 2)
    (hstrong : HasStrongSolver p (hierarchyGamma p i)
      (hierarchyStrongLogPower i)) :
    HasResidualSolver p (hierarchyGamma p (i + 1))
      (hierarchyResidualLogPower (i + 1)) := by
  obtain ⟨S, hS⟩ := hstrong
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
  obtain ⟨A, hA⟩ := boostClaim_proof p S (hierarchyGamma p i)
    (hierarchyStrongLogPower i) hS hierarchyGamma_pos hgamma1
    ha23 ha2
  refine ⟨A, ?_⟩
  rw [hierarchyGamma_succ, ← hierarchy_log_power_boost]
  exact hA

/-- Final assembly with only the restart edge left as an input.  Once
`restartClaim_proof` is imported, the final theorem is a direct application
of this lemma.  For `p=2` the restart range is empty. -/
theorem mainTheoremClaim_of_restart
    (hrestart : ∀ p, 2 ≤ p → ∀ j, 1 ≤ j → j ≤ p - 2 →
      HasResidualSolver p (hierarchyGamma p j) (hierarchyResidualLogPower j) →
      HasStrongSolver p (hierarchyGamma p j) (hierarchyStrongLogPower j)) :
    MainTheoremClaim := by
  apply mainTheoremClaim_of_transformations
  · intro p hp
    exact hierarchy_base_hasStrong p
  · intro p hp i hi
    exact hierarchy_boost_hasResidual p hp i hi
  · exact hrestart

theorem hierarchy_restart_hasStrong (p : ℕ) (hp : 2 ≤ p) (j : ℕ)
    (_hj0 : 1 ≤ j) (_hjp : j ≤ p - 2)
    (hresidual : HasResidualSolver p (hierarchyGamma p j)
      (hierarchyResidualLogPower j)) :
    HasStrongSolver p (hierarchyGamma p j) (hierarchyStrongLogPower j) := by
  obtain ⟨A, hA⟩ := hresidual
  have hgamma0 : 0 < hierarchyGamma p j := hierarchyGamma_pos
  have hgamma1 : hierarchyGamma p j ≤ 1 := by
    unfold hierarchyGamma
    apply (div_le_one (by positivity : (0 : ℝ) < p + 1 + 2 * j)).2
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
    push_cast
    linarith
  obtain ⟨S, hS⟩ := restartClaim_proof p A (hierarchyGamma p j)
    (hierarchyResidualLogPower j) hA hgamma0 hgamma1
  refine ⟨S, ?_⟩
  simpa [hierarchyStrongLogPower, hierarchyResidualLogPower] using hS

/-- Unconditional closure of the matching theorem package from the actual
base, boost, and restart implementations. -/
theorem mainTheoremClaim_proof : MainTheoremClaim := by
  exact mainTheoremClaim_of_restart (fun p hp j hj0 hjp hresidual ↦
    hierarchy_restart_hasStrong p hp j hj0 hjp hresidual)

end

end VIReference.Pilot
