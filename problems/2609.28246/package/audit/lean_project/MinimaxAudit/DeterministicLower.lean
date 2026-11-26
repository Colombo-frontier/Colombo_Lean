import MinimaxAudit.LowerScaling
import MinimaxAudit.SourceGap

/-! End-to-end finite-budget deterministic scalar-jet tangent lower bound.
The algorithm is the manuscript's total-history unrestricted policy. The
constructed objective is the concrete scalar potential with proved admissibility;
its output can be feasible and unqueried. -/

open scoped ContDiff

namespace MinimaxAudit

/-- Actual transcript, analytic class, and tangent obstruction on the same
single completed paired frame. -/
theorem deterministic_tangent_hard_frame {p N : ℕ} (profile : GateProfile)
    (hp : 2 ≤ p) {L R : ℝ} (hL : 0 < L) (hR : 0 < R)
    (A : DeterministicScalarPolicy p (2 * N + 2) (2 * N + 2) N
      (Metric.closedBall (0 : Primal (2 * N + 2)) R)
      (Metric.closedBall (0 : Dual (2 * N + 2)) R)) :
    ∃ (U : Fin (N + 1) → Primal (2 * N + 2)) (V : Fin (N + 1) → Dual (2 * N + 2))
      (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V),
    let phi := minimaxHardPotential profile (hardGateWidth N R) (hardAmplitude profile p N L R)
      (balancedQ N) (hardSeed N R) hU hV
    let output := Deterministic.runScalarPolicy A (exactScalarJet p phi) N []
    AdmissibleScalar p L (2 * Real.sqrt 2 * R)
      (Metric.closedBall (0 : Primal (2 * N + 2)) R)
      (Metric.closedBall (0 : Dual (2 * N + 2)) R) phi ∧
    Metric.diam (productDomain (Metric.closedBall (0 : Primal (2 * N + 2)) R)
      (Metric.closedBall (0 : Dual (2 * N + 2)) R)) = 2 * Real.sqrt 2 * R ∧
    pairedA U V (Fin.last N) output = 0 ∧
    hardAmplitude profile p N L R * hardSeed N R / (2 * Real.sqrt (N + 1)) ≤
      auditedTangentResidual
        (productDomain (Metric.closedBall (0 : Primal (2 * N + 2)) R)
          (Metric.closedBall (0 : Dual (2 * N + 2)) R)) (scalarSaddleOperator phi) output := by
  let c := hardSeed N R
  let tau := hardGateWidth N R
  let lam := hardAmplitude profile p N L R
  have hc := hardSeed_pos N hR
  have htau := hardGateWidth_pos N hR
  have hlam := hardAmplitude_pos profile p N hL hR
  obtain ⟨U, V, hU, hV, hout⟩ := Deterministic.exists_paired_resisting_zero_coordinates
    profile htau lam c (balancedQ N) A le_rfl le_rfl
  let phi := minimaxHardPotential profile tau lam (balancedQ N) c hU hV
  have hpotential : Deterministic.hardPotential profile tau lam c (balancedQ N) U V = phi :=
    deterministic_potential_eq profile tau lam c (balancedQ N) hU hV
  change Deterministic.plusForm U V (Fin.last N)
    (Deterministic.runScalarPolicy A (exactScalarJet p (Deterministic.hardPotential profile tau lam c (balancedQ N) U V)) N []) = 0 ∧ _ at hout
  rw [hpotential] at hout
  have ha : pairedA U V (Fin.last N) (Deterministic.runScalarPolicy A (exactScalarJet p phi) N []) = 0 := hout.1
  have hfeasible := Deterministic.runScalarPolicy_feasible A (exactScalarJet p phi) N []
  refine ⟨U, V, hU, hV, hardInstance_admissible profile hp hL hR hU hV,
    productBall_diameter_exact hR.le hU hV, ha, ?_⟩
  apply source_tangent_residual_lower hU hV profile htau hlam hR rfl rfl _ hfeasible
  rw [ha, abs_zero]
  exact htau.le

/-- Diameter-normalized obstruction with an explicit positive p-only constant
once the cutoff profile is fixed to standardGateProfile. -/
theorem deterministic_tangent_lower_standard {p N : ℕ} (hp : 2 ≤ p)
    {L D : ℝ} (hL : 0 < L) (hD : 0 < D)
    (A : DeterministicScalarPolicy p (2 * N + 2) (2 * N + 2) N
      (Metric.closedBall (0 : Primal (2 * N + 2)) (D / (2 * Real.sqrt 2)))
      (Metric.closedBall (0 : Dual (2 * N + 2)) (D / (2 * Real.sqrt 2)))) :
    ∃ phi : SaddleSpace (2 * N + 2) (2 * N + 2) → ℝ,
      AdmissibleScalar p L D
        (Metric.closedBall (0 : Primal (2 * N + 2)) (D / (2 * Real.sqrt 2)))
        (Metric.closedBall (0 : Dual (2 * N + 2)) (D / (2 * Real.sqrt 2))) phi ∧
      Metric.diam (productDomain
        (Metric.closedBall (0 : Primal (2 * N + 2)) (D / (2 * Real.sqrt 2)))
        (Metric.closedBall (0 : Dual (2 * N + 2)) (D / (2 * Real.sqrt 2)))) = D ∧
      tangentRateConstant standardGateProfile p * L * D ^ p /
        (N + 1 : ℝ) ^ oracleRateExponent p ≤
      auditedTangentResidual
        (productDomain
          (Metric.closedBall (0 : Primal (2 * N + 2)) (D / (2 * Real.sqrt 2)))
          (Metric.closedBall (0 : Dual (2 * N + 2)) (D / (2 * Real.sqrt 2))))
        (scalarSaddleOperator phi) (Deterministic.runScalarPolicy A (exactScalarJet p phi) N []) := by
  let R := D / (2 * Real.sqrt 2)
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨U, V, hU, hV, hadm, hdiam, ha, hlower⟩ :=
    deterministic_tangent_hard_frame standardGateProfile hp hL hR A
  have hscale : 2 * Real.sqrt 2 * R = D := by
    dsimp [R]
    field_simp
  rw [hscale] at hadm hdiam
  refine ⟨_, hadm, hdiam, ?_⟩
  rw [hard_tangent_scale standardGateProfile hp N L D] at hlower
  exact hlower

/-- Source quantifier order for the deterministic tangent part of main(i).
The constant depends only on the fixed derivative order. -/
theorem deterministic_tangent_lower (p : ℕ) (hp : 2 ≤ p) :
    ∃ a : ℝ, 0 < a ∧ ∀ N : ℕ, 1 ≤ N → ∀ L D : ℝ, 0 < L → 0 < D →
      ∀ A : DeterministicScalarPolicy p (2 * N + 2) (2 * N + 2) N
        (Metric.closedBall (0 : Primal (2 * N + 2)) (D / (2 * Real.sqrt 2)))
        (Metric.closedBall (0 : Dual (2 * N + 2)) (D / (2 * Real.sqrt 2))),
      ∃ phi : SaddleSpace (2 * N + 2) (2 * N + 2) → ℝ,
        AdmissibleScalar p L D
          (Metric.closedBall (0 : Primal (2 * N + 2)) (D / (2 * Real.sqrt 2)))
          (Metric.closedBall (0 : Dual (2 * N + 2)) (D / (2 * Real.sqrt 2))) phi ∧
        a * L * D ^ p / (N + 1 : ℝ) ^ oracleRateExponent p ≤
          auditedTangentResidual
            (productDomain
              (Metric.closedBall (0 : Primal (2 * N + 2)) (D / (2 * Real.sqrt 2)))
              (Metric.closedBall (0 : Dual (2 * N + 2)) (D / (2 * Real.sqrt 2))))
            (scalarSaddleOperator phi) (Deterministic.runScalarPolicy A (exactScalarJet p phi) N []) := by
  refine ⟨tangentRateConstant standardGateProfile p, tangentRateConstant_pos standardGateProfile p, ?_⟩
  intro N _ L D hL hD A
  obtain ⟨phi, hadm, hdiam, htan⟩ := deterministic_tangent_lower_standard hp hL hD A
  exact ⟨phi, hadm, htan⟩

/-- Both source criteria hold for the same fixed deterministic hard instance. -/
theorem deterministic_lower_standard {p N : ℕ} (hp : 2 ≤ p)
    {L D : ℝ} (hL : 0 < L) (hD : 0 < D)
    (A : DeterministicScalarPolicy p (2 * N + 2) (2 * N + 2) N
      (Metric.closedBall (0 : Primal (2 * N + 2)) (D / (2 * Real.sqrt 2)))
      (Metric.closedBall (0 : Dual (2 * N + 2)) (D / (2 * Real.sqrt 2)))) :
    ∃ phi : SaddleSpace (2 * N + 2) (2 * N + 2) → ℝ,
      AdmissibleScalar p L D
        (Metric.closedBall (0 : Primal (2 * N + 2)) (D / (2 * Real.sqrt 2)))
        (Metric.closedBall (0 : Dual (2 * N + 2)) (D / (2 * Real.sqrt 2))) phi ∧
      Metric.diam (productDomain
        (Metric.closedBall (0 : Primal (2 * N + 2)) (D / (2 * Real.sqrt 2)))
        (Metric.closedBall (0 : Dual (2 * N + 2)) (D / (2 * Real.sqrt 2)))) = D ∧
      let output := Deterministic.runScalarPolicy A (exactScalarJet p phi) N []
      tangentRateConstant standardGateProfile p * L * D ^ p /
        (N + 1 : ℝ) ^ oracleRateExponent p ≤
        auditedTangentResidual
          (productDomain
            (Metric.closedBall (0 : Primal (2 * N + 2)) (D / (2 * Real.sqrt 2)))
            (Metric.closedBall (0 : Dual (2 * N + 2)) (D / (2 * Real.sqrt 2))))
          (scalarSaddleOperator phi) output ∧
      gapRateConstant standardGateProfile p * L * D ^ (p + 1) /
        (N + 1 : ℝ) ^ oracleRateExponent p ≤
        auditedSaddleGap
          (Metric.closedBall (0 : Primal (2 * N + 2)) (D / (2 * Real.sqrt 2)))
          (Metric.closedBall (0 : Dual (2 * N + 2)) (D / (2 * Real.sqrt 2)))
          (fun x y => phi (joinBlocks x y)) (primalBlock output) (dualBlock output) := by
  let R := D / (2 * Real.sqrt 2)
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨U, V, hU, hV, hadm, hdiam, ha, htan⟩ :=
    deterministic_tangent_hard_frame standardGateProfile hp hL hR A
  let phi := minimaxHardPotential standardGateProfile (hardGateWidth N R)
    (hardAmplitude standardGateProfile p N L R) (balancedQ N) (hardSeed N R) hU hV
  let output := Deterministic.runScalarPolicy A (exactScalarJet p phi) N []
  have hfeasible := Deterministic.runScalarPolicy_feasible A (exactScalarJet p phi) N []
  have hsmall : |pairedA U V (Fin.last N) output| ≤ hardGateWidth N R := by
    change |pairedA U V (Fin.last N) (Deterministic.runScalarPolicy A (exactScalarJet p phi) N [])| ≤ _
    rw [ha, abs_zero]
    exact (hardGateWidth_pos N hR).le
  have hgap := source_product_gap_lower hU hV standardGateProfile (c := hardSeed N R)
    (hardGateWidth_pos N hR) (hardAmplitude_pos standardGateProfile p N hL hR) hR
    rfl rfl output hfeasible hsmall
  have hscale : 2 * Real.sqrt 2 * R = D := by dsimp [R]; field_simp
  rw [hscale] at hadm hdiam
  rw [hard_tangent_scale standardGateProfile hp N L D] at htan
  rw [hard_gap_scale standardGateProfile hp N L D] at hgap
  exact ⟨phi, hadm, hdiam, htan, hgap⟩

/-- Global source main(i) refinement: the same concrete hard instance is globally
C∞, globally convex-concave, and globally highest-derivative Lipschitz. -/
theorem deterministic_lower_global_standard {p N : ℕ} (hp : 2 ≤ p)
    {L D : ℝ} (hL : 0 < L) (hD : 0 < D)
    (A : DeterministicScalarPolicy p (2 * N + 2) (2 * N + 2) N
      (Metric.closedBall (0 : Primal (2 * N + 2)) (D / (2 * Real.sqrt 2)))
      (Metric.closedBall (0 : Dual (2 * N + 2)) (D / (2 * Real.sqrt 2)))) :
    ∃ phi : SaddleSpace (2 * N + 2) (2 * N + 2) → ℝ,
      AdmissibleScalar p L D
        (Metric.closedBall (0 : Primal (2 * N + 2)) (D / (2 * Real.sqrt 2)))
        (Metric.closedBall (0 : Dual (2 * N + 2)) (D / (2 * Real.sqrt 2))) phi ∧
      ContDiff ℝ ∞ phi ∧
      (∀ y : Dual (2 * N + 2), ConvexOn ℝ Set.univ (fun x => phi (joinBlocks x y))) ∧
      (∀ x : Primal (2 * N + 2), ConcaveOn ℝ Set.univ (fun y => phi (joinBlocks x y))) ∧
      (∀ z w : SaddleSpace (2 * N + 2) (2 * N + 2),
        ‖iteratedFDeriv ℝ p phi z - iteratedFDeriv ℝ p phi w‖ ≤ L * ‖z - w‖) ∧
      Metric.diam (productDomain
        (Metric.closedBall (0 : Primal (2 * N + 2)) (D / (2 * Real.sqrt 2)))
        (Metric.closedBall (0 : Dual (2 * N + 2)) (D / (2 * Real.sqrt 2)))) = D ∧
      let output := Deterministic.runScalarPolicy A (exactScalarJet p phi) N []
      tangentRateConstant standardGateProfile p * L * D ^ p /
        (N + 1 : ℝ) ^ oracleRateExponent p ≤
        auditedTangentResidual
          (productDomain
            (Metric.closedBall (0 : Primal (2 * N + 2)) (D / (2 * Real.sqrt 2)))
            (Metric.closedBall (0 : Dual (2 * N + 2)) (D / (2 * Real.sqrt 2))))
          (scalarSaddleOperator phi) output ∧
      gapRateConstant standardGateProfile p * L * D ^ (p + 1) /
        (N + 1 : ℝ) ^ oracleRateExponent p ≤
        auditedSaddleGap
          (Metric.closedBall (0 : Primal (2 * N + 2)) (D / (2 * Real.sqrt 2)))
          (Metric.closedBall (0 : Dual (2 * N + 2)) (D / (2 * Real.sqrt 2)))
          (fun x y => phi (joinBlocks x y)) (primalBlock output) (dualBlock output) := by
  let R := D / (2 * Real.sqrt 2)
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨U, V, hU, hV, hadm, hdiam, ha, htan⟩ :=
    deterministic_tangent_hard_frame standardGateProfile hp hL hR A
  let phi := minimaxHardPotential standardGateProfile (hardGateWidth N R)
    (hardAmplitude standardGateProfile p N L R) (balancedQ N) (hardSeed N R) hU hV
  let output := Deterministic.runScalarPolicy A (exactScalarJet p phi) N []
  have hglobal := hardInstance_global standardGateProfile hp hL hR hU hV
  have hfeasible := Deterministic.runScalarPolicy_feasible A (exactScalarJet p phi) N []
  have hsmall : |pairedA U V (Fin.last N) output| ≤ hardGateWidth N R := by
    change |pairedA U V (Fin.last N) (Deterministic.runScalarPolicy A (exactScalarJet p phi) N [])| ≤ _
    rw [ha, abs_zero]
    exact (hardGateWidth_pos N hR).le
  have hgap := source_product_gap_lower hU hV standardGateProfile (c := hardSeed N R)
    (hardGateWidth_pos N hR) (hardAmplitude_pos standardGateProfile p N hL hR) hR
    rfl rfl output hfeasible hsmall
  have hscale : 2 * Real.sqrt 2 * R = D := by dsimp [R]; field_simp
  rw [hscale] at hadm hdiam
  rw [hard_tangent_scale standardGateProfile hp N L D] at htan
  rw [hard_gap_scale standardGateProfile hp N L D] at hgap
  exact ⟨phi, hadm, hglobal.1, hglobal.2.1, hglobal.2.2.1, hglobal.2.2.2, hdiam, htan, hgap⟩

/-- Source main(i): p-only positive constants, exact d_x=d_y=2N+2 and D,
complete scalar jets, arbitrary adaptive feasible query/output rules, both
criteria on the same fixed admissible scalar instance. -/
theorem deterministic_lower_source (p : ℕ) (hp : 2 ≤ p) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ N : ℕ, 1 ≤ N → ∀ L D : ℝ, 0 < L → 0 < D →
      ∀ A : DeterministicScalarPolicy p (2 * N + 2) (2 * N + 2) N
        (Metric.closedBall (0 : Primal (2 * N + 2)) (D / (2 * Real.sqrt 2)))
        (Metric.closedBall (0 : Dual (2 * N + 2)) (D / (2 * Real.sqrt 2))),
      ∃ phi : SaddleSpace (2 * N + 2) (2 * N + 2) → ℝ,
        AdmissibleScalar p L D
          (Metric.closedBall (0 : Primal (2 * N + 2)) (D / (2 * Real.sqrt 2)))
          (Metric.closedBall (0 : Dual (2 * N + 2)) (D / (2 * Real.sqrt 2))) phi ∧
        Metric.diam (productDomain
          (Metric.closedBall (0 : Primal (2 * N + 2)) (D / (2 * Real.sqrt 2)))
          (Metric.closedBall (0 : Dual (2 * N + 2)) (D / (2 * Real.sqrt 2)))) = D ∧
        let output := Deterministic.runScalarPolicy A (exactScalarJet p phi) N []
        a * L * D ^ p / (N + 1 : ℝ) ^ oracleRateExponent p ≤
          auditedTangentResidual
            (productDomain
              (Metric.closedBall (0 : Primal (2 * N + 2)) (D / (2 * Real.sqrt 2)))
              (Metric.closedBall (0 : Dual (2 * N + 2)) (D / (2 * Real.sqrt 2))))
            (scalarSaddleOperator phi) output ∧
        b * L * D ^ (p + 1) / (N + 1 : ℝ) ^ oracleRateExponent p ≤
          auditedSaddleGap
            (Metric.closedBall (0 : Primal (2 * N + 2)) (D / (2 * Real.sqrt 2)))
            (Metric.closedBall (0 : Dual (2 * N + 2)) (D / (2 * Real.sqrt 2)))
            (fun x y => phi (joinBlocks x y)) (primalBlock output) (dualBlock output) := by
  refine ⟨tangentRateConstant standardGateProfile p, gapRateConstant standardGateProfile p,
    tangentRateConstant_pos standardGateProfile p, gapRateConstant_pos standardGateProfile p, ?_⟩
  intro N _ L D hL hD A
  exact deterministic_lower_standard hp hL hD A

end MinimaxAudit
