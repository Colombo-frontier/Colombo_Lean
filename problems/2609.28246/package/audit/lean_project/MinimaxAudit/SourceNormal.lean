import MinimaxAudit.SourceGeometry

/-! Full product-ball tangent obstruction for the actual scalar hard instance.
The zero is constructed by contraction; its interior radius is derived from the
actual gate recurrence. The tangent residual is the true normal-cone infimum. -/

namespace MinimaxAudit

/-- Strictly interior primal and dual blocks admit an ambient Euclidean ball. -/
theorem source_productBall_ambient_interior {dx dy : ℕ} {R : ℝ}
    {z : SaddleSpace dx dy} (hx : ‖primalBlock z‖ < R) (hy : ‖dualBlock z‖ < R) :
    ∃ r > 0, Metric.ball z r ⊆
      productDomain (Metric.closedBall (0 : Primal dx) R) (Metric.closedBall (0 : Dual dy) R) := by
  let r := min (R - ‖primalBlock z‖) (R - ‖dualBlock z‖)
  have hr : 0 < r := lt_min (sub_pos.mpr hx) (sub_pos.mpr hy)
  refine ⟨r, hr, ?_⟩
  intro w hw
  have hd : ‖w - z‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have hxp := (source_block_norms_le (w - z)).1
  have hyp := (source_block_norms_le (w - z)).2
  rw [source_primal_sub] at hxp
  rw [source_dual_sub] at hyp
  have hxnorm := norm_sub_norm_le (primalBlock w) (primalBlock z)
  have hynorm := norm_sub_norm_le (dualBlock w) (dualBlock z)
  have hminx : r ≤ R - ‖primalBlock z‖ := min_le_left _ _
  have hminy : r ≤ R - ‖dualBlock z‖ := min_le_right _ _
  change ‖primalBlock w - 0‖ ≤ R ∧ ‖dualBlock w - 0‖ ≤ R
  simp only [sub_zero]
  constructor <;> linarith

/-- On the actual product-ball interior the true tangent residual is ‖F‖. -/
theorem source_tangent_interior_eq {dx dy : ℕ} {R : ℝ} {z : SaddleSpace dx dy}
    (hx : ‖primalBlock z‖ < R) (hy : ‖dualBlock z‖ < R)
    (F : SaddleSpace dx dy → SaddleSpace dx dy) :
    auditedTangentResidual
      (productDomain (Metric.closedBall (0 : Primal dx) R) (Metric.closedBall (0 : Dual dy) R)) F z = ‖F z‖ := by
  obtain ⟨r, hr, hball⟩ := source_productBall_ambient_interior hx hy
  exact tangent_residual_eq_norm_of_ball hr hball

/-- Either boundary block is at least 7R/8 from an R/8-interior ambient zero. -/
theorem source_boundary_distance {dx dy : ℕ} {R : ℝ} {z zstar : SaddleSpace dx dy}
    (hstar : ‖zstar‖ ≤ R / 8)
    (hboundary : ‖primalBlock z‖ = R ∨ ‖dualBlock z‖ = R) :
    7 * R / 8 ≤ ‖z - zstar‖ := by
  have hblocks := source_block_norms_le zstar
  rcases hboundary with hx | hy
  · have h := boundary_distance_lower hx (hblocks.1.trans hstar)
    exact h.trans (by simpa using (source_block_norms_le (z - zstar)).1)
  · have h := boundary_distance_lower hy (hblocks.2.trans hstar)
    exact h.trans (by simpa using (source_block_norms_le (z - zstar)).2)

/-- The boundary strong-monotonicity scale dominates the paper's desired
half-seed residual scale for its explicit κ. -/
theorem source_boundary_scale {n : ℕ} {lam R c : ℝ}
    (hlam : 0 ≤ lam) (hR : 0 ≤ R)
    (hc : c = geometryKappa * R / Real.sqrt (n + 1)) :
    lam * c / (2 * Real.sqrt (n + 1)) ≤
      (lam * (1 - balancedQ n)) * (7 * R / 8) := by
  have hN : (0 : ℝ) < n + 1 := by positivity
  have hratio : c / Real.sqrt (n + 1) = geometryKappa * R / (n + 1 : ℝ) := by
    rw [hc, div_div, ← pow_two, Real.sq_sqrt hN.le]
  have hnonneg : 0 ≤ lam * R / (n + 1 : ℝ) := by positivity
  have hnumeric := explicit_boundary_residual_constant (lam * R / (n + 1 : ℝ)) hnonneg
  have hleft : lam * c / (2 * Real.sqrt (n + 1)) =
      geometryKappa * (lam * R / (n + 1 : ℝ)) / 2 := by
    calc
      _ = (lam / 2) * (c / Real.sqrt (n + 1)) := by ring
      _ = _ := by rw [hratio]; ring
  have hright : (lam * (1 - balancedQ n)) * (7 * R / 8) =
      7 * (lam * R / (n + 1 : ℝ)) / 32 := by
    unfold balancedQ
    field_simp
    ring
  rwa [hleft, hright]

section Actual
variable {n dx dy : ℕ} {U : Fin (n + 1) → Primal dx} {V : Fin (n + 1) → Dual dy}
variable (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V)

/-- The actual scalar zero has both blocks feasible in the public product balls. -/
theorem source_inner_zero_feasible {R : ℝ} (hR : 0 ≤ R) {zstar : SaddleSpace dx dy}
    (hstar : ‖zstar‖ ≤ R / 8) :
    zstar ∈ productDomain (Metric.closedBall (0 : Primal dx) R) (Metric.closedBall (0 : Dual dy) R) := by
  have hb := source_block_norms_le zstar
  change ‖primalBlock zstar - 0‖ ≤ R ∧ ‖dualBlock zstar - 0‖ ≤ R
  simp only [sub_zero]
  constructor <;> linarith [hb.1, hb.2]

/-- Boundary part of the normal obstruction, using the actual signed gradient
and an actual zero of that scalar potential. -/
theorem source_boundary_tangent_lower (profile : GateProfile) {tau lam c R : ℝ}
    (htau : 0 < tau) (hlam : 0 < lam) (hR : 0 < R)
    (hc : c = geometryKappa * R / Real.sqrt (n + 1))
    (zstar : SaddleSpace dx dy)
    (hzero : scalarSaddleOperator (minimaxHardPotential profile tau lam (balancedQ n) c hU hV) zstar = 0)
    (hstar : ‖zstar‖ ≤ R / 8) (z : SaddleSpace dx dy)
    (hboundary : ‖primalBlock z‖ = R ∨ ‖dualBlock z‖ = R) :
    lam * c / (2 * Real.sqrt (n + 1)) ≤
      auditedTangentResidual
        (productDomain (Metric.closedBall (0 : Primal dx) R) (Metric.closedBall (0 : Dual dy) R))
        (scalarSaddleOperator (minimaxHardPotential profile tau lam (balancedQ n) c hU hV)) z := by
  have hmu : 0 ≤ lam * (1 - balancedQ n) :=
    mul_nonneg hlam.le (sub_nonneg.mpr (balancedQ_le_one n))
  have hzstar := source_inner_zero_feasible hR.le hstar
  have hs := minimaxHardPotential_strong_monotone profile (c := c) htau.ne'
    (balancedQ_nonneg n) hlam.le hU hV z zstar
  have hd := source_boundary_distance hstar hboundary
  exact (source_boundary_scale hlam.le hR.le hc).trans
    (strong_zero_tangent_residual_bound hmu hzstar hzero hs hd)

/-- The full manuscript product-ball tangent obstruction for the concrete
scalar objective. The witness zero is constructed, not supplied as a premise. -/
theorem source_tangent_residual_lower (profile : GateProfile) {tau lam c R : ℝ}
    (htau : 0 < tau) (hlam : 0 < lam) (hR : 0 < R)
    (hc : c = geometryKappa * R / Real.sqrt (n + 1))
    (ht : tau = geometryEta * c / (n + 1 : ℝ))
    (z : SaddleSpace dx dy)
    (hz : z ∈ productDomain (Metric.closedBall (0 : Primal dx) R) (Metric.closedBall (0 : Dual dy) R))
    (hr : |pairedA U V (Fin.last n) z| ≤ tau) :
    lam * c / (2 * Real.sqrt (n + 1)) ≤
      auditedTangentResidual
        (productDomain (Metric.closedBall (0 : Primal dx) R) (Metric.closedBall (0 : Dual dy) R))
        (scalarSaddleOperator (minimaxHardPotential profile tau lam (balancedQ n) c hU hV)) z := by
  have hq0 := balancedQ_nonneg n
  have hq1 := balancedQ_le_one n
  have hqlt : balancedQ n < 1 := by
    unfold balancedQ
    have hd : (0 : ℝ) < 1 / (4 * (n + 1 : ℝ)) := by positivity
    linarith
  have hc0 : 0 ≤ c := by rw [hc]; unfold geometryKappa; positivity
  have he := framedHardPotential_exists_unique_zero profile (c := c) htau.ne' hq0 hqlt hlam
    (euclideanSaddleSign dx dy) (euclideanSaddleSign_involutive dx dy)
    (blockPairedFrame_orthonormal hU hV) (Fin.last n)
  obtain ⟨zstar, hzero, _⟩ := he
  have hzero' : scalarSaddleOperator
      (minimaxHardPotential profile tau lam (balancedQ n) c hU hV) zstar = 0 := hzero
  have hstar := source_zero_inner_radius hU hV profile htau hlam hq0 hq1 hR hc ht zstar hzero'
  change ‖primalBlock z - 0‖ ≤ R ∧ ‖dualBlock z - 0‖ ≤ R at hz
  simp only [sub_zero] at hz
  by_cases hx : ‖primalBlock z‖ < R
  · by_cases hy : ‖dualBlock z‖ < R
    · rw [source_tangent_interior_eq hx hy]
      exact source_balanced_scalar_residual hU hV profile htau hlam.le hc0 ht z hr
    · exact source_boundary_tangent_lower hU hV profile htau hlam hR hc zstar hzero' hstar z
        (Or.inr (le_antisymm hz.2 (le_of_not_gt hy)))
  · exact source_boundary_tangent_lower hU hV profile htau hlam hR hc zstar hzero' hstar z
      (Or.inl (le_antisymm hz.1 (le_of_not_gt hx)))

end Actual

end MinimaxAudit
