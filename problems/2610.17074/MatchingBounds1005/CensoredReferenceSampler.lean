import MatchingBounds1005.CensoredGaussianProcess
import MatchingBounds1005.FiniteGaussianSampler

/-!
# Private-noise realization of the actual censored reference

The reference experiment can be run deterministically from a finite Gaussian
seed independent of the rotation and the algorithm's initial seed. The
rotation is retained in the joint law but is not an input to an innovation
response except through its explicit visible signal and measurement rows.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace MatchingBounds1005.CensoredReferenceSampler
open GaussianVector SequentialPosterior CensoredGaussianProcess FiniteGaussianSampler

variable {Ω : Type*} [MeasurableSpace Ω] {d T : ℕ}

def sample (A : CensoredProtocol Ω d T) (σ : ℝ) (n : ℕ) :
    Ω × Noise d n → History Ω T n :=
  run (fun k => response A σ k (A.visible k)) n

theorem sample_measurable (A : CensoredProtocol Ω d T) (σ : ℝ) (n : ℕ) :
    Measurable (sample A σ n) :=
  run_measurable _ (fun k => response_measurable A σ k _ (A.measurable_visible k)) n

theorem sample_law (A : CensoredProtocol Ω d T) (σ : ℝ)
    (ν₀ : Measure Ω) [IsProbabilityMeasure ν₀] (n : ℕ) :
    (ν₀.prod (noiseLaw d n)).map (sample A σ n) = referenceLaw A σ ν₀ n :=
  run_law _ (fun k => response_measurable A σ k _ (A.measurable_visible k)) ν₀ n

variable {U W : Type*} [MeasurableSpace U] [MeasurableSpace W]

def privateSample (A : CensoredProtocol (U × W) d T) (σ : ℝ) (n : ℕ) :
    U × (W × Noise d n) → History (U × W) T n :=
  fun p => sample A σ n ((p.1, p.2.1), p.2.2)

theorem privateSample_measurable (A : CensoredProtocol (U × W) d T) (σ : ℝ) (n : ℕ) :
    Measurable (privateSample A σ n) :=
  (sample_measurable A σ n).comp MeasurableEquiv.prodAssoc.symm.measurable

/-- The complete private seed `(algorithm seed, Gaussian noises)` is
independent of `U` under an actual product measure. Reading it generates
exactly the reference joint transcript used in the KL comparison. -/
theorem privateSample_law (A : CensoredProtocol (U × W) d T) (σ : ℝ)
    (νU : Measure U) (νW : Measure W) [IsProbabilityMeasure νU] [IsProbabilityMeasure νW]
    (n : ℕ) :
    (νU.prod (νW.prod (noiseLaw d n))).map (privateSample A σ n) =
      referenceLaw A σ (νU.prod νW) n := by
  have h : Measurable (fun p : U × (W × Noise d n) => sample A σ n ((p.1, p.2.1), p.2.2)) :=
    privateSample_measurable A σ n
  rw [← sample_law]
  change (νU.prod (νW.prod (noiseLaw d n))).map
    (fun p => sample A σ n ((p.1, p.2.1), p.2.2)) = _
  rw [← Measure.prodAssoc_prod, Measure.map_map h MeasurableEquiv.prodAssoc.measurable]
  rfl

end MatchingBounds1005.CensoredReferenceSampler
