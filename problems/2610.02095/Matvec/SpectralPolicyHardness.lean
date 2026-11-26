import Matvec.SpectralHardness
import Matvec.MeasurableOracleAdapter

/-! The main spectral lower bound for the ordinary finite-transcript Policy
interface used by all executable oracle reductions. -/
namespace Matvec
open Matrix MeasureTheory LowRank MeasurableSimulation
open scoped Matrix
noncomputable section
universe u

theorem adaptive_gaussian_policy_spectral_lower_bound :
    ∃ γ : ℝ, 0 < γ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ t : ℕ, 8 * t ≤ N →
      ∀ (S : Type u) [MeasurableSpace S] (ν : Measure S), IsProbabilityMeasure ν →
      ∀ (alg : Policy (AmbientQuery N N) (AmbientQuery N N) ℝ t S),
      γ ≤ (ν.prod (iidMatrixLaw N N 1)).real
        {x | alg.run (fun q => (x.2 *ᵥ q.2, x.2ᵀ *ᵥ q.1)) x.1 ∉
          Set.Icc (leastStretch (matrixEuclideanMap x.2) / 2)
            (2 * leastStretch (matrixEuclideanMap x.2))} := by
  obtain ⟨γ, hγ, N₀, h⟩ := adaptive_gaussian_spectral_lower_bound.{u}
  refine ⟨γ, hγ, N₀, ?_⟩
  intro N hN t ht S inst ν hν alg
  have hh := h N hN t ht S ν hν (alg.toTwoSided t) (alg.nestedOutput t)
    (alg.measurable_nestedOutput t)
  simpa only [Policy.toTwoSided_replay] using hh

end
end Matvec
