import Matvec.GaussianSourceEstimator

/-! A concrete measurable Gaussian spectral-estimation policy from an
ordinary source solver, with its exact all-transcript query cap and success law. -/
namespace Matvec
open Matrix MeasureTheory LowRank MeasurableSimulation SourceIterationPolicy
open scoped Matrix
noncomputable section

def sourceSpectralPolicy {n K : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (base : Policy (DilationSpace n) (DilationSpace n) (DilationSpace n) K
      (DilationSpace n × Seed)) (a : ℝ) (R S : ℕ) :=
  gaussianSourcePolicy ((maximumPolicy (estimatorPolicy base R) S).mapOutput
    (fun _ x => reciprocalSpectralEstimate n a x)
    (by
      unfold reciprocalSpectralEstimate
      exact measurable_const.div (measurable_const.mul measurable_snd))) a

def sourceSpectralLaw (n : ℕ) {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) (R S : ℕ) :=
  Measure.pi (fun _ : Fin (S + 1) => sourceEstimatorLaw (E := DilationSpace n) μ R)

instance sourceSpectralLaw_probability (n : ℕ) {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (R S : ℕ) :
    IsProbabilityMeasure (sourceSpectralLaw n μ R S) := by
  unfold sourceSpectralLaw
  infer_instance

theorem sourceSpectralPolicy_run {n K : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (base : Policy (DilationSpace n) (DilationSpace n) (DilationSpace n) K
      (DilationSpace n × Seed)) (a : ℝ) (R S : ℕ)
    (G : Matrix (Fin n) (Fin n) ℝ) (seeds) :
    (sourceSpectralPolicy base a R S).run (fun q => (G *ᵥ q.2, Gᵀ *ᵥ q.1)) seeds =
      reciprocalSpectralEstimate n a
        (repeatedMaximum (sourceEstimator (gaussianSourceMap G a)
          (fun r s => base.run (gaussianSourceMap G a) (r, s)) R) S seeds) := by
  rw [sourceSpectralPolicy, gaussianSourcePolicy_run, Policy.mapOutput_run, maximumPolicy_run]
  have heq : (estimatorPolicy base R).run (gaussianSourceMap G a) =
      sourceEstimator (gaussianSourceMap G a)
        (fun r s => base.run (gaussianSourceMap G a) (r, s)) R := by
    funext seed
    exact estimatorPolicy_run base (gaussianSourceMap G a) R seed
  rw [heq]

theorem sourceSpectralPolicy_reliable {n K : ℕ} (hn : 0 < n)
    {Seed : Type*} [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (base : Policy (DilationSpace n) (DilationSpace n) (DilationSpace n) K
      (DilationSpace n × Seed)) (a : ℝ) (ha : 0 < a)
    (ε : ℝ) (hε : 0 < ε) (S : ℕ)
    (hS : (1 - sourceStartProbability / 2) ^ (S + 1) ≤ ε / 2)
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : Function.Injective G.mulVec)
    (hH : (gaussianSourceMap G a).toLinearMap.IsSymmetric)
    (hexpand : ∀ w, ‖w‖ ≤ ‖gaussianSourceMap G a w‖)
    (hsuccess : ∀ r, 3 / 5 ≤ μ.real
      {s | ‖gaussianSourceMap G a (base.run (gaussianSourceMap G a) (r, s)) - r‖ ≤ ‖r‖ / 2}) :
    let d := Module.finrank ℝ (DilationSpace n)
    let q := inversePowerLengthFor sourceStartComponent d
    let J := refinementLength (inversePowerAccuracyFor sourceStartComponent d)
    let θ := min (sourceStartProbability / 2) (ε / (2 * (S + 1 : ℝ)))
    let R := sourceVerificationLength θ q J
    1 - ε ≤ (sourceSpectralLaw n μ R S).real
      {seeds | (sourceSpectralPolicy base a R S).run (fun q => (G *ᵥ q.2, Gᵀ *ᵥ q.1)) seeds ∈
        Set.Icc (leastStretch (matrixEuclideanMap G) / 2)
          (2 * leastStretch (matrixEuclideanMap G))} := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨M, hHM, hMH⟩ := exists_inverse_of_expansion (gaussianSourceMap G a) hexpand
  have hbase : Measurable (fun p : DilationSpace n × Seed =>
      base.run (gaussianSourceMap G a) (p.1, p.2)) :=
    base.measurable_run _ (gaussianSourceMap G a).continuous.measurable
  have hd : 2 ≤ Module.finrank ℝ (DilationSpace n) := by
    simp only [DilationSpace, finrank_euclideanSpace, Fintype.card_sum, Fintype.card_fin]
    omega
  have h := sourceEstimator_reliable_of_start_count ε hε S hS μ
    (gaussianSourceMap G a) M hH hHM hMH
    (fun r s => base.run (gaussianSourceMap G a) (r, s)) hbase hsuccess hd
  dsimp only at h ⊢
  apply h.trans
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro seeds hs
  dsimp only [Set.mem_setOf_eq] at hs ⊢
  rw [sourceSpectralPolicy_run]
  exact gaussianSource_reciprocal_success hn G hG a ha M hHM hMH hs

end
end Matvec
