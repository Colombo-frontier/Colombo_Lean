import Matvec.OrdinarySourceHardness
import Matvec.SourceIsometryTransport
import Matvec.SourceEstimatorComplexity
import Matvec.RateArithmetic

/-! The ordinary source-solve query lower bound at the manuscript's
N/(log² N log log N) rate, with arbitrary fixed Euclidean coordinates.
The estimator overhead and the removal of the additive query constant are
both proved, rather than assumed asymptotic cost bounds. -/
namespace Matvec
open MeasureTheory MeasurableSimulation
noncomputable section
universe u v

theorem ordinary_source_solver_rate_lower_bound :
    ∃ κ c : ℝ, 0 < κ ∧ 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [MeasurableSpace E] [BorelSpace E],
      ∀ (_e : DilationSpace N ≃ₗᵢ[ℝ] E), ∀ K : ℕ,
      ∀ (Seed : Type u) [MeasurableSpace Seed] (μ : Measure Seed), IsProbabilityMeasure μ →
      ∀ (base : Policy E E E K (E × Seed)),
      (∀ H : E →L[ℝ] E, H.toLinearMap.IsSymmetric →
        (∀ w, ‖w‖ ≤ ‖H w‖) → ‖H‖ ≤ κ * N →
        ∀ r, 3 / 5 ≤ μ.real {s | ‖H (base.run H (r, s)) - r‖ ≤ ‖r‖ / 2}) →
      c * sourceRate N ≤ K := by
  obtain ⟨a, κ, ε, _, _, hκ, hε, _, S, N₁, _, hexact⟩ :=
    ordinary_source_solver_query_lower_bound.{u}
  let θ := min (sourceStartProbability / 2) (ε / (2 * (S + 1 : ℝ)))
  have hθ : 0 < θ := lt_min (half_pos sourceStart_constants_pos.2) (by positivity)
  obtain ⟨C, hC, hcost⟩ := source_estimator_policy_cost_bound sourceStartComponent θ
    sourceStart_constants_pos.1 hθ S
  obtain ⟨N₂, hlarge⟩ := sourceRate_large (128 * C)
  refine ⟨κ, 1 / (128 * C), hκ, by positivity, max (max N₁ N₂) 7, ?_⟩
  intro N hN E instNorm instInner instMeas instBorel e K Seed instSeed μ hμ base hsolve
  have hN₁ : N₁ ≤ N := (le_max_left N₁ N₂).trans ((le_max_left _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_right N₁ N₂).trans ((le_max_left _ _).trans hN)
  have hN7 : 7 ≤ N := (le_max_right _ _).trans hN
  have hs := hexact N hN₁ K Seed μ hμ (transportSourcePolicy e base)
    (transportSourcePolicy_success e base μ (κ * N) hsolve)
  have hd : Module.finrank ℝ (DilationSpace N) = 2 * N := by
    simp only [DilationSpace, finrank_euclideanSpace, Fintype.card_sum, Fintype.card_fin]
    omega
  rw [hd] at hs
  let q := inversePowerLengthFor sourceStartComponent (2 * N)
  let J := refinementLength (inversePowerAccuracyFor sourceStartComponent (2 * N))
  let R := sourceVerificationLength θ q J
  let budget := (S + 1) * (q * (J * ((R + 1) * (K + 1) + 1)))
  change N < 8 * budget at hs
  have hsR : (N : ℝ) ≤ 8 * (budget : ℝ) := by exact_mod_cast hs.le
  have hc := hcost (2 * N) K (by omega : 14 ≤ 2 * N)
  change (budget : ℝ) ≤ C * Real.log (((2 * N : ℕ) : ℝ) + 2) ^ 2 *
    Real.log (Real.log (((2 * N : ℕ) : ℝ) + 2)) * (K + 1 : ℝ) at hc
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hc
  have hden := doubled_dimension_denominator_bound N
  have hc' : (budget : ℝ) ≤ (8 * C) * sourceDenominator N * (K + 1 : ℝ) := by
    apply hc.trans
    calc
      _ = C * (Real.log (2 * (N : ℝ) + 2) ^ 2 *
          Real.log (Real.log (2 * (N : ℝ) + 2))) * (K + 1 : ℝ) := by ring
      _ ≤ C * (8 * sourceDenominator N) * (K + 1 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hden hC.le) (by positivity)
      _ = _ := by ring
  have hNbound := hsR.trans (mul_le_mul_of_nonneg_left hc' (by norm_num : (0 : ℝ) ≤ 8))
  have hrate : sourceRate N ≤ (64 * C) * (K + 1 : ℝ) := by
    change (N : ℝ) / sourceDenominator N ≤ _
    apply (div_le_iff₀ (sourceDenominator_pos N)).mpr
    convert hNbound using 1; ring
  have hlarge' : 2 * (64 * C) ≤ sourceRate N := by
    convert hlarge N hN₂ using 1; ring
  have h := absorb_query_add_one (by positivity : 0 < 64 * C) hlarge' hrate
  convert h using 1; ring

end
end Matvec
