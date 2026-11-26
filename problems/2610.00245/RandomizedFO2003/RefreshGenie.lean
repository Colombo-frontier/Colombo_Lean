import RandomizedFO2003.GenieEvents
import RandomizedFO2003.PairRefresh

namespace RandomizedFO2003.Cascade

open SpectralCoordinates Rotations

noncomputable def refreshSample {J : ℕ} (K : Fin J → ℕ) (N : ℕ) (i : Fin (N + 1))
    (p : Sample K N) (u : BlockSpace K) (U : Rotation (BlockSpace K)) : Sample K N :=
  (Function.update p.1 i u, Function.update p.2 i U)

end RandomizedFO2003.Cascade

namespace RandomizedFO2003.FiniteSpectralDesign

open MeasureTheory SpectralCoordinates Cascade Rotations Spherical
open scoped BigOperators

variable {m : ℕ} {γ L : ℝ} (S : FiniteSpectralDesign m γ L (1 / (16 * γ)))

/-- The public coefficients ignore both refreshed coordinates, including
the old latent direction; every other block remains exactly as sampled. -/
theorem publicCascadeCoefficients_refresh (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (i : Fin (N + 1)) (p : Sample K N) (u : BlockSpace K) (U : Rotation (BlockSpace K)) :
    S.publicCascadeCoefficients K N h i (refreshSample K N i p u U) =
      S.publicCascadeCoefficients K N h i p := by
  apply Prod.ext
  · funext j
    by_cases hji : j = i
    · subst j
      simp only [publicCascadeCoefficients, decoderCoefficients, Function.update_self]
    · simp only [publicCascadeCoefficients, decoderCoefficients, cascadeCoefficients,
        refreshSample, Function.update_of_ne hji]
  · apply Prod.ext
    · funext j
      by_cases hji : j = i
      · subst j
        simp only [publicCascadeCoefficients, decoderCoefficients, Function.update_self]
      · simp only [publicCascadeCoefficients, decoderCoefficients, cascadeCoefficients,
          refreshSample, Function.update_of_ne hji]
    · funext j
      by_cases hji : j = i
      · subst j
        simp only [publicCascadeCoefficients, decoderCoefficients, Function.update_self]
      · simp only [publicCascadeCoefficients, decoderCoefficients, cascadeCoefficients,
          refreshSample, Function.update_of_ne hji]

variable {Seed : Type} [MeasurableSpace Seed]

theorem refreshSample_seed_preserving (K : Fin S.size → ℕ) (N : ℕ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin (N + 1)) :
    MeasurePreserving
      (fun p : (BlockSpace K × (Sample K N × Seed)) × Rotation (BlockSpace K) =>
        (refreshSample K N i p.1.2.1 p.1.1 p.2, p.1.2.2))
      (((sphereLaw (BlockSpace K)).prod ((S.cascadeParameterLaw K N).prod ν)).prod (haarLaw (BlockSpace K)))
      ((S.cascadeParameterLaw K N).prod ν) :=
  pi_pair_refresh_seed_preserving (sphereLaw (BlockSpace K)) (haarLaw (BlockSpace K)) ν i

/-- Executing the genie on the refreshed sample is exactly execution with
the new independent mark/rotation and the old public background. -/
theorem censoredGenieHistory_refresh (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (T : ℕ) (i : Fin (N + 1))
    (p : Sample K N) (u : BlockSpace K) (U : Rotation (BlockSpace K)) (seed : Seed) :
    S.censoredGenieHistory K N h A T i (refreshSample K N i p u U).1 (refreshSample K N i p u U).2 seed =
      ((S.censoredGenieProgram K N h A T i).compile (continuousDiagonal K S.node) (T + 1) Prod.fst
        measurable_fst).run (markedActionCount (T + 1)) (U : BlockSpace K →L[ℝ] BlockSpace K)
          (u, S.publicCascadeCoefficients K N h i p, seed) := by
  change ((S.censoredGenieProgram K N h A T i).compile (continuousDiagonal K S.node) (T + 1) Prod.fst
    measurable_fst).run (markedActionCount (T + 1))
      ((refreshSample K N i p u U).2 i : BlockSpace K →L[ℝ] BlockSpace K)
      ((refreshSample K N i p u U).1 i,
        S.publicCascadeCoefficients K N h i (refreshSample K N i p u U), seed) = _
  rw [S.publicCascadeCoefficients_refresh]
  simp only [refreshSample, Function.update_self]

end RandomizedFO2003.FiniteSpectralDesign
