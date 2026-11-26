import Matvec.SourceSpectralReduction
import Matvec.SourceJointProbability
import Matvec.PolicyJointMeasurable
import Matvec.GaussianSourceProbability

/-! The ordinary randomized source-solve lower bound, obtained from an
executed measurable source-to-spectral policy and the actual Gaussian input
distribution. The conclusion records the exact estimator budget, before
simplifying its logarithmic factors. -/
namespace Matvec
open Matrix MeasureTheory LowRank MeasurableSimulation SourceIterationPolicy
open scoped Matrix
noncomputable section
universe u

theorem ordinary_source_solver_query_lower_bound :
    ∃ a κ ε : ℝ, 0 < a ∧ a ≤ 1 ∧ 0 < κ ∧ 0 < ε ∧ ε ≤ 1 ∧
      ∃ S N₀ : ℕ,
      (1 - sourceStartProbability / 2) ^ (S + 1) ≤ ε / 2 ∧
      ∀ N ≥ N₀, ∀ K : ℕ, ∀ (Seed : Type u) [MeasurableSpace Seed]
        (μ : Measure Seed), IsProbabilityMeasure μ →
      ∀ (base : Policy (DilationSpace N) (DilationSpace N) (DilationSpace N) K
        (DilationSpace N × Seed)),
      (∀ H : DilationSpace N →L[ℝ] DilationSpace N,
        H.toLinearMap.IsSymmetric → (∀ w, ‖w‖ ≤ ‖H w‖) → ‖H‖ ≤ κ * N →
        ∀ r, 3 / 5 ≤ μ.real {s | ‖H (base.run H (r, s)) - r‖ ≤ ‖r‖ / 2}) →
      let d := Module.finrank ℝ (DilationSpace N)
      let q := inversePowerLengthFor sourceStartComponent d
      let J := refinementLength (inversePowerAccuracyFor sourceStartComponent d)
      let θ := min (sourceStartProbability / 2) (ε / (2 * (S + 1 : ℝ)))
      let R := sourceVerificationLength θ q J
      N < 8 * ((S + 1) * (q * (J * ((R + 1) * (K + 1) + 1)))) := by
  obtain ⟨γ, hγ, N₁, hspectral⟩ := adaptive_gaussian_policy_spectral_lower_bound.{u}
  let ε := min (γ / 4) (1 / 4)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hεγ : 2 * ε < γ := by
    have h := min_le_left (γ / 4) (1 / 4 : ℝ)
    change ε ≤ γ / 4 at h
    linarith
  obtain ⟨a, κ, ha, ha1, hκ, hpromise⟩ := gaussian_source_reliable_promise ε hε
  obtain ⟨S, hS⟩ := exists_source_start_repetitions ε hε
  refine ⟨a, κ, ε, ha, ha1, hκ, hε, hε1, S, max N₁ 1, hS, ?_⟩
  intro N hN K Seed inst μ hμ base hsolve
  letI := hμ
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hNpos : 0 < N := by have := (le_max_right N₁ 1).trans hN; omega
  cases N with
  | zero => omega
  | succ n =>
    let d := Module.finrank ℝ (DilationSpace (n + 1))
    let q := inversePowerLengthFor sourceStartComponent d
    let J := refinementLength (inversePowerAccuracyFor sourceStartComponent d)
    let θ := min (sourceStartProbability / 2) (ε / (2 * (S + 1 : ℝ)))
    let R := sourceVerificationLength θ q J
    let T := (S + 1) * (q * (J * ((R + 1) * (K + 1) + 1)))
    let alg := sourceSpectralPolicy base a R S
    let EstSeed := Fin (S + 1) → (Fin d → ℝ) ×
      SeedBlock (SeedBlock (Fin (R + 1) → Seed) J) q
    let ν := sourceSpectralLaw (n + 1) μ R S
    let ρ := iidMatrixLaw (n + 1) (n + 1) 1
    haveI : IsProbabilityMeasure ν := sourceSpectralLaw_probability _ μ _ _
    haveI : IsProbabilityMeasure ρ := iidMatrixLaw_probability _ _ _
    let Good := {G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ |
      ((gaussianSourceMap G a).toLinearMap.IsSymmetric ∧
        (∀ w, ‖w‖ ≤ ‖gaussianSourceMap G a w‖) ∧
        ‖gaussianSourceMap G a‖ ≤ κ * (n + 1 : ℝ)) ∧ Function.Injective G.mulVec}
    have hGood : 1 - ε ≤ ρ.real Good := by
      apply (hpromise n).trans
      apply ENNReal.toReal_mono (measure_ne_top ρ _)
      apply measure_mono_ae
      filter_upwards [iidMatrixLaw_mulVec_injective_ae (n + 1) (n + 1) le_rfl
        (by norm_num : (1 : NNReal) ≠ 0)] with G hG
      intro hGp
      exact ⟨hGp, hG⟩
    let F := {p : EstSeed × Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ |
      alg.run (fun z => (p.2 *ᵥ z.2, p.2ᵀ *ᵥ z.1)) p.1 ∈
      Set.Icc (leastStretch (matrixEuclideanMap p.2) / 2)
        (2 * leastStretch (matrixEuclideanMap p.2))}
    have hrun := alg.joint_measurable_ambient_run
    have hscore : Measurable (fun p : EstSeed × Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
        leastStretch (matrixEuclideanMap p.2)) :=
      (measurable_matrix_leastStretch (n + 1) (n + 1) (by omega)).comp measurable_snd
    have hF : MeasurableSet F := by
      exact (measurableSet_le (hscore.div_const 2) hrun).inter
        (measurableSet_le hrun (hscore.const_mul 2))
    have hpoint : ∀ G ∈ Good, 1 - ε ≤ ν.real {s | (s, G) ∈ F} := by
      intro G hG
      have hs := sourceSpectralPolicy_reliable (by omega) μ base a ha ε hε S hS G hG.2
        hG.1.1 hG.1.2.1 (hsolve (gaussianSourceMap G a) hG.1.1 hG.1.2.1
          (by simpa only [Nat.cast_succ] using hG.1.2.2))
      exact hs
    have hupper : (ν.prod ρ).real Fᶜ ≤ ε + ε :=
      product_failure_of_pointwise ν ρ F hF Good ε ε hε.le hε1 hε.le hGood hpoint
    change n + 1 < 8 * T
    by_contra hcap
    have ht : 8 * T ≤ n + 1 := by omega
    have hlower := hspectral (n + 1) hN₁ T ht _ ν inferInstance alg
    change γ ≤ (ν.prod ρ).real Fᶜ at hlower
    linarith

end
end Matvec
