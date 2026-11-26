import Matvec
import Lean.Util.CollectAxioms

/-! Expanded statements prevent a weakened target definition from silently
passing. The foundation audit follows both types and proof values. -/
namespace MatvecAudit
open Matvec MeasureTheory LowRank Matvec.MeasurableSimulation
open scoped Matrix

theorem mainSequenceStatement :
    ∃ c₀ c₁ c₂ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (∀ (T : ℕ) (Seed : Type) [MeasurableSpace Seed]
        (alg : Algorithm (4 * N) (2 * N + 1) T Seed) (μ : Measure Seed),
        IsProbabilityMeasure μ →
        Solves alg μ .ballSimplex (c₀ / (N : ℝ) ^ (3 / 2 : ℝ)) →
        c₂ * (N / ((Real.log (N + 2)) ^ 2 *
          Real.log (Real.log (N + Real.exp (Real.exp 1))))) ≤ T) ∧
      (∀ (T : ℕ) (Seed : Type) [MeasurableSpace Seed]
        (alg : Algorithm (4 * N) (4 * N) T Seed) (μ : Measure Seed),
        IsProbabilityMeasure μ →
        Solves alg μ .simplexSimplex
          (c₁ / ((N : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log (N + 2)))) →
        c₂ * (N / ((Real.log (N + 2)) ^ 2 *
          Real.log (Real.log (N + Real.exp (Real.exp 1))))) ≤ T) :=
  main_sequence_lower_bounds

theorem accuracyRateStatement :
  (∃ C a b ε₀ : ℝ, 0 < C ∧ 0 < a ∧ 0 < b ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ N : ℕ, 0 < N ∧
      a * ε ^ (-(2 / 3 : ℝ)) ≤ N ∧ (N : ℝ) ≤ b * ε ^ (-(2 / 3 : ℝ)) ∧
      ∀ m n : ℕ, 4 * N ≤ m → 2 * N + 1 ≤ n →
        ∀ (T : ℕ) (Seed : Type) [MeasurableSpace Seed]
          (alg : Algorithm m n T Seed) (μ : Measure Seed), IsProbabilityMeasure μ →
          Solves alg μ .ballSimplex ε →
          C * (ε ^ (-(2 / 3 : ℝ)) /
            (Real.log ε⁻¹ ^ 2 * Real.log (Real.log ε⁻¹))) ≤ T) ∧
  (∃ C a b ε₀ : ℝ, 0 < C ∧ 0 < a ∧ 0 < b ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ N : ℕ, 0 < N ∧
      a * (ε ^ (-(2 / 3 : ℝ)) / (Real.log ε⁻¹) ^ (1 / 3 : ℝ)) ≤ N ∧
      (N : ℝ) ≤ b * (ε ^ (-(2 / 3 : ℝ)) / (Real.log ε⁻¹) ^ (1 / 3 : ℝ)) ∧
      ∀ m n : ℕ, 4 * N ≤ m → 4 * N ≤ n →
        ∀ (T : ℕ) (Seed : Type) [MeasurableSpace Seed]
          (alg : Algorithm m n T Seed) (μ : Measure Seed), IsProbabilityMeasure μ →
          Solves alg μ .simplexSimplex ε →
          C * (ε ^ (-(2 / 3 : ℝ)) /
            ((Real.log ε⁻¹) ^ (7 / 3 : ℝ) * Real.log (Real.log ε⁻¹))) ≤ T) :=
  high_dimensional_rates

theorem ordinarySourceStatement :
    ∃ κ c : ℝ, 0 < κ ∧ 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [MeasurableSpace E] [BorelSpace E],
      ∀ (_e : DilationSpace N ≃ₗᵢ[ℝ] E), ∀ K : ℕ,
      ∀ (Seed : Type) [MeasurableSpace Seed] (μ : Measure Seed), IsProbabilityMeasure μ →
      ∀ (base : Policy E E E K (E × Seed)),
      (∀ H : E →L[ℝ] E, H.toLinearMap.IsSymmetric →
        (∀ w, ‖w‖ ≤ ‖H w‖) → ‖H‖ ≤ κ * N →
        ∀ r, 3 / 5 ≤ μ.real {s | ‖H (base.run H (r, s)) - r‖ ≤ ‖r‖ / 2}) →
      c * (N / ((Real.log (N + 2)) ^ 2 *
        Real.log (Real.log (N + Real.exp (Real.exp 1))))) ≤ K :=
  ordinary_source_solver_rate_lower_bound

theorem spectralStatement :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N : ℕ, 0 < N → ∀ t : ℕ, 8 * t ≤ N →
      ∀ (Seed : Type) [MeasurableSpace Seed] (ν : Measure Seed), IsProbabilityMeasure ν →
      ∀ (policy : TwoSidedOraclePolicy N N t Seed)
        (output : TwoSidedOracleHistory N N t Seed → ℝ), Measurable output →
      γ ≤ (ν.prod (iidMatrixLaw N N 1)).real
        {x | output (runTwoSidedOracle N N t policy x.2 x.1) ∉
          Set.Icc (leastStretch (matrixEuclideanMap x.2) / 2)
            (2 * leastStretch (matrixEuclideanMap x.2))} :=
  adaptive_gaussian_spectral_lower_bound_all_dimensions

theorem spectralPolicyStatement :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N : ℕ, 0 < N → ∀ t : ℕ, 8 * t ≤ N →
      ∀ (Seed : Type) [MeasurableSpace Seed] (ν : Measure Seed), IsProbabilityMeasure ν →
      ∀ (alg : Policy (AmbientQuery N N) (AmbientQuery N N) ℝ t Seed),
      γ ≤ (ν.prod (iidMatrixLaw N N 1)).real
        {x | alg.run (fun q => (x.2 *ᵥ q.2, x.2ᵀ *ᵥ q.1)) x.1 ∉
          Set.Icc (leastStretch (matrixEuclideanMap x.2) / 2)
            (2 * leastStretch (matrixEuclideanMap x.2))} :=
  adaptive_gaussian_policy_spectral_lower_bound_all_dimensions

end MatvecAudit

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, info) in env.constants.toList do
    if name.getRoot == `Matvec || name.toString.startsWith "_private.Matvec." then
      match info with
      | .thmInfo _ => names := names.push name
      | _ => pure ()
  names := names.qsort (fun a b => a.toString < b.toString)
  if names.isEmpty then throwError "No Matvec theorems found."
  let assertions := #[`MatvecAudit.mainSequenceStatement, `MatvecAudit.accuracyRateStatement,
    `MatvecAudit.ordinarySourceStatement, `MatvecAudit.spectralStatement,
    `MatvecAudit.spectralPolicyStatement]
  -- Reuse the visited set across all dependency closures. Lean's collector
  -- reads the checked kernel environment, including dependencies of types.
  let (_, state) := (((names ++ assertions).forM Lean.CollectAxioms.collect).run env).run {}
  let unexpected := state.axioms.filter (fun a =>
    a != `propext && a != `Classical.choice && a != `Quot.sound)
  unless unexpected.isEmpty do
    throwError "Unexpected transitive dependencies: {unexpected}"
  logInfo m!"Transitive foundations: {state.axioms}"
  let headlines := #[`Matvec.main_sequence_lower_bounds, `Matvec.high_dimensional_rates,
    `Matvec.ordinary_source_solver_rate_lower_bound,
    `Matvec.adaptive_gaussian_spectral_lower_bound_all_dimensions,
    `Matvec.adaptive_gaussian_policy_spectral_lower_bound_all_dimensions]
  for name in headlines do
    match env.checked.get.find? name with
    | some (.thmInfo info) => logInfo m!"HEADLINE TYPE: {name}\n{info.type}"
    | _ => throwError "Required headline is not a checked theorem: {name}"
  for name in names do
    logInfo m!"PASS {name}"
  for name in assertions do
    logInfo m!"STATEMENT PASSED: {name}"
  logInfo "HEADLINE PASSED: Matvec.main_sequence_lower_bounds"
  logInfo "HEADLINE PASSED: Matvec.high_dimensional_rates"
  logInfo "HEADLINE PASSED: Matvec.ordinary_source_solver_rate_lower_bound"
  logInfo "HEADLINE PASSED: Matvec.adaptive_gaussian_spectral_lower_bound_all_dimensions"
  logInfo "POLICY WRAPPER PASSED: Matvec.adaptive_gaussian_policy_spectral_lower_bound_all_dimensions"
  logInfo m!"AUDIT PASSED: {names.size} Matvec theorem constants; standard foundations only."
