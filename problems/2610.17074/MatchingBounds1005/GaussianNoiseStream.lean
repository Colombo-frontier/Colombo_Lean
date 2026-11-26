import MatchingBounds1005.FiniteGaussianSampler

/-!
# Reading the finite private Gaussian seed by physical query number

The same fixed finite seed supplies all round-indexed Gaussian draws. The
resulting stream execution is proved equal to the actual sampler execution.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace MatchingBounds1005.GaussianNoiseStream
open GaussianVector SequentialPosterior FiniteGaussianSampler

def noiseAt {d : ℕ} : (N : ℕ) → Noise d N → ℕ → Vec d
  | 0, _, _ => 0
  | N + 1, z, i => if i = N then z.2 else noiseAt N z.1 i

theorem noiseAt_measurable (d N i : ℕ) : Measurable (fun z : Noise d N => noiseAt N z i) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
      by_cases hi : i = N
      · simpa only [noiseAt, if_pos hi] using (measurable_snd : Measurable (Prod.snd : Noise d N × Vec d → Vec d))
      · simpa only [noiseAt, if_neg hi] using ih.comp measurable_fst

variable {Ω : Type*} [MeasurableSpace Ω] {d T : ℕ}

def runStream (f : (n : ℕ) → History Ω T n × Vec d → Fin T → ℝ)
    (seed : Ω) (noise : ℕ → Vec d) : (n : ℕ) → History Ω T n
  | 0 => seed
  | n + 1 => (runStream f seed noise n, f n (runStream f seed noise n, noise n))

theorem runStream_congr (f : (n : ℕ) → History Ω T n × Vec d → Fin T → ℝ)
    (seed : Ω) (noise noise' : ℕ → Vec d) (n : ℕ)
    (heq : ∀ i < n, noise i = noise' i) : runStream f seed noise n = runStream f seed noise' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [runStream, runStream, ih (fun i hi => heq i (Nat.lt_succ_of_lt hi)), heq n (Nat.lt_succ_self n)]

theorem runStream_noiseAt (f : (n : ℕ) → History Ω T n × Vec d → Fin T → ℝ)
    (seed : Ω) (n : ℕ) (noise : Noise d n) :
    runStream f seed (noiseAt n noise) n = run f n (seed, noise) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hprev : runStream f seed (noiseAt (n + 1) noise) n = runStream f seed (noiseAt n noise.1) n := by
        apply runStream_congr
        intro i hi
        exact if_neg (Nat.ne_of_lt hi)
      rw [runStream, hprev, ih noise.1]
      simp only [noiseAt, if_pos rfl, ite_true, run]

/-- Fixed private-seed execution has exactly the actual Gaussian-kernel
transcript law, with no fresh randomness exposed to the algorithm in advance. -/
theorem runStream_law (f : (n : ℕ) → History Ω T n × Vec d → Fin T → ℝ)
    (hf : ∀ n, Measurable (f n)) (ν₀ : Measure Ω) [IsProbabilityMeasure ν₀] (n : ℕ) :
    (ν₀.prod (noiseLaw d n)).map (fun p => runStream f p.1 (noiseAt n p.2) n) =
      SeededKernelKL.transcriptLaw (fun k => GaussianKernel.observationKernel (f k) (hf k)) ν₀ n := by
  simp only [runStream_noiseAt]
  exact run_law f hf ν₀ n

end MatchingBounds1005.GaussianNoiseStream
