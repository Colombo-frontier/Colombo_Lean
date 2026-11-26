import MatchingBounds1005.GaussianKernel
import MatchingBounds1005.SeededKernelKL

/-!
# A private finite Gaussian seed for the actual reference process

All Gaussian draws can be sampled independently of the joint initial seed
before the algorithm begins. Deterministically reading this finite noise
tree has exactly the previously constructed Gaussian-kernel transcript law.
This supplies private randomness for the accessible Haar-policy interface.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace MatchingBounds1005.FiniteGaussianSampler
open GaussianVector GaussianKernel SequentialPosterior

def Noise (d : ℕ) : ℕ → Type
  | 0 => Unit
  | n + 1 => Noise d n × Vec d

instance noiseMeasurableSpace (d n : ℕ) : MeasurableSpace (Noise d n) :=
  match n with
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | n + 1 =>
      letI := noiseMeasurableSpace d n
      inferInstanceAs (MeasurableSpace (Noise d n × Vec d))

def noiseLaw (d : ℕ) : (n : ℕ) → Measure (Noise d n)
  | 0 => Measure.dirac ()
  | n + 1 => (noiseLaw d n).prod (standardGaussian d)

instance noiseLaw_probability (d n : ℕ) : IsProbabilityMeasure (noiseLaw d n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | succ n ih =>
      letI := ih
      exact inferInstanceAs (IsProbabilityMeasure ((noiseLaw d n).prod (standardGaussian d)))

variable {Ω : Type*} [MeasurableSpace Ω] {d T : ℕ}

def run (f : (n : ℕ) → History Ω T n × Vec d → (Fin T → ℝ)) :
    (n : ℕ) → Ω × Noise d n → History Ω T n
  | 0, p => p.1
  | n + 1, p =>
      let h := run f n (p.1, p.2.1)
      (h, f n (h, p.2.2))

theorem run_measurable (f : (n : ℕ) → History Ω T n × Vec d → (Fin T → ℝ))
    (hf : ∀ n, Measurable (f n)) (n : ℕ) : Measurable (run f n) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
      have hprevious : Measurable (fun p : Ω × (Noise d n × Vec d) => run f n (p.1, p.2.1)) :=
        ih.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
      exact hprevious.prodMk ((hf n).comp (hprevious.prodMk (measurable_snd.comp measurable_snd)))

/-- A single independent private Gaussian seed realizes the actual adaptive
kernel law exactly. No conditional Gaussian identity is assumed. -/
theorem run_law (f : (n : ℕ) → History Ω T n × Vec d → (Fin T → ℝ))
    (hf : ∀ n, Measurable (f n)) (ν₀ : Measure Ω) [IsProbabilityMeasure ν₀] (n : ℕ) :
    (ν₀.prod (noiseLaw d n)).map (run f n) =
      SeededKernelKL.transcriptLaw (fun k => observationKernel (f k) (hf k)) ν₀ n := by
  induction n with
  | zero =>
      change (ν₀.prod (Measure.dirac ())).map Prod.fst = ν₀
      simp
  | succ n ih =>
      let step := fun p : History Ω T n × Vec d => (p.1, f n p)
      have hs : Measurable step := measurable_fst.prodMk (hf n)
      have hrun : Measurable (fun p : Ω × (Noise d n × Vec d) =>
          step (run f n (p.1, p.2.1), p.2.2)) := run_measurable f hf (n + 1)
      change (ν₀.prod ((noiseLaw d n).prod (standardGaussian d))).map
        (fun p => step (run f n (p.1, p.2.1), p.2.2)) = _
      calc
        _ = ((ν₀.prod (noiseLaw d n)).prod (standardGaussian d)).map
            (fun p => step (run f n p.1, p.2)) := by
          rw [← Measure.prodAssoc_prod, Measure.map_map hrun MeasurableEquiv.prodAssoc.measurable]
          rfl
        _ = (((ν₀.prod (noiseLaw d n)).map (run f n)).prod (standardGaussian d)).map step :=
          (map_prod_right _ _ (run f n) (run_measurable f hf n) step hs).symm
        _ = _ := by
          rw [ih, SeededKernelKL.transcriptLaw, observationKernel_compProd]

end MatchingBounds1005.FiniteGaussianSampler
