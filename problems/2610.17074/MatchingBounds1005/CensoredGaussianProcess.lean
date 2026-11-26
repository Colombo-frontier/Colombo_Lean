import MatchingBounds1005.ShiftedSequential
import MatchingBounds1005.GaussianRows
import MatchingBounds1005.GaussianKernel
import MatchingBounds1005.SeededKernelKL

/-!
# Actual censored Gaussian transcript comparison

The true experiment draws one signal-plus-Gaussian parameter and keeps it
fixed. The reference uses the same minimum-norm fitted old observations and
censors only the unobserved signal. Both are actual probability laws. Their
joint transcript KL is derived from the static posterior and kernel chain
rule. A disclosure/Haar instantiation is separate from this theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped InnerProductSpace ENNReal NNReal

namespace MatchingBounds1005.CensoredGaussianProcess
open GaussianVector AdaptiveGaussian GaussianFitter PosteriorGaussian
open SequentialPosterior GaussianRows GaussianKernel InnovationGaussianKL

variable {Ω : Type*} [MeasurableSpace Ω] {d T : ℕ}

structure CensoredProtocol (Ω : Type*) [MeasurableSpace Ω] (d T : ℕ) where
  original : ShiftedSequential.ShiftedProtocol Ω d T
  visible : (n : ℕ) → History Ω T n → Vec d
  measurable_visible : ∀ n, Measurable (visible n)

def hidden (A : CensoredProtocol Ω d T) (n : ℕ) (h : History Ω T n) : Vec d :=
  A.original.signal (ShiftedSequential.initialSeed n h) - A.visible n h

attribute [local irreducible] projection fitter rowResponse Submodule.span
  Submodule.orthogonalProjection Submodule.orthogonal

def response (A : CensoredProtocol Ω d T) (σ : ℝ) (n : ℕ)
    (signal : History Ω T n → Vec d) (p : History Ω T n × Vec d) : Fin T → ℝ :=
  rowResponse (A.original.rowProtocol.rows n p.1)
    (fittedMean A.original.rowProtocol.rows n p.1 +
      projection (exposure A.original.rowProtocol.rows n p.1)ᗮ (signal p.1 + σ • p.2))

theorem response_measurable (A : CensoredProtocol Ω d T) (σ : ℝ) (n : ℕ)
    (signal : History Ω T n → Vec d) (hs : Measurable signal) :
    Measurable (response A σ n signal) := by
  have hin : Measurable (fun p : History Ω T n × Vec d => (p.1, signal p.1 + σ • p.2)) :=
    measurable_fst.prodMk ((hs.comp measurable_fst).add (measurable_const.smul measurable_snd))
  have hQ := (measurable_complement (exposure A.original.rowProtocol.rows n)
    (measurable_exposure A.original.rowProtocol n)).comp hin
  have hfit : Measurable (fun p : History Ω T n × Vec d => fittedMean A.original.rowProtocol.rows n p.1) :=
    (measurable_fittedMean A.original.rowProtocol n).comp measurable_fst
  have hp := (measurable_fst : Measurable (Prod.fst : History Ω T n × Vec d → History Ω T n)).prodMk (hfit.add hQ)
  exact (measurable_rowResponse_family (A.original.rowProtocol.rows n)
    (A.original.rowProtocol.measurable_rows n)).comp hp

def referenceKernel (A : CensoredProtocol Ω d T) (σ : ℝ) (n : ℕ) :
    Kernel (History Ω T n) (Fin T → ℝ) :=
  observationKernel (response A σ n (A.visible n))
    (response_measurable A σ n _ (A.measurable_visible n))

def trueKernel (A : CensoredProtocol Ω d T) (σ : ℝ) (n : ℕ) :
    Kernel (History Ω T n) (Fin T → ℝ) :=
  observationKernel
    (response A σ n (fun h => A.original.signal (ShiftedSequential.initialSeed n h)))
    (response_measurable A σ n _
      (A.original.measurable_signal.comp (ShiftedSequential.initialSeed_measurable n)))

instance referenceKernel_markov (A : CensoredProtocol Ω d T) (σ : ℝ) (n : ℕ) :
    IsMarkovKernel (referenceKernel A σ n) := inferInstanceAs
      (IsMarkovKernel (observationKernel _ _))

instance trueKernel_markov (A : CensoredProtocol Ω d T) (σ : ℝ) (n : ℕ) :
    IsMarkovKernel (trueKernel A σ n) := inferInstanceAs
      (IsMarkovKernel (observationKernel _ _))

def innovation (A : CensoredProtocol Ω d T) (n : ℕ) (h : History Ω T n) :
    Submodule ℝ (Vec d) :=
  innovationSpace (rowMap (A.original.rowProtocol.rows n h))
    (exposure A.original.rowProtocol.rows n h)

theorem innovation_eq (A : CensoredProtocol Ω d T) (n : ℕ) (h : History Ω T n) :
    innovation A n h = exposure A.original.rowProtocol.rows (n + 1) (h, (0 : Fin T → ℝ)) ⊓
      (exposure A.original.rowProtocol.rows n h)ᗮ :=
  innovationSpace_rowMap _ _ (A.original.rowProtocol.nested n h)

def energyCost (A : CensoredProtocol Ω d T) (σ : ℝ) (n : ℕ) (h : History Ω T n) : ℝ :=
  ‖(innovation A n h).orthogonalProjection (hidden A n h)‖ ^ 2 / (2 * σ ^ 2)

theorem energyCost_nonneg (A : CensoredProtocol Ω d T) (σ : ℝ) (n : ℕ)
    (h : History Ω T n) : 0 ≤ energyCost A σ n h := by
  unfold energyCost
  positivity

/-- Exact KL between the actual censored and true transition measures. -/
theorem conditional_klDiv (A : CensoredProtocol Ω d T) {σ : ℝ} (hσ : σ ≠ 0)
    (n : ℕ) (h : History Ω T n) :
    klDiv (referenceKernel A σ n h) (trueKernel A σ n h) =
      ENNReal.ofReal (energyCost A σ n h) := by
  have heq := censored_innovation_klDiv (rowMap (A.original.rowProtocol.rows n h))
    (exposure A.original.rowProtocol.rows n h) (fittedMean A.original.rowProtocol.rows n h)
    (A.visible n h) (hidden A n h) hσ
  have hs : A.visible n h + hidden A n h =
      A.original.signal (ShiftedSequential.initialSeed n h) := by
    unfold hidden
    abel
  rw [hs] at heq
  simpa only [referenceKernel, trueKernel, observationKernel_apply, response, rowMap_apply,
    energyCost, innovation] using heq

theorem conditional_klDiv_le (A : CensoredProtocol Ω d T) {σ : ℝ} (hσ : σ ≠ 0)
    (n : ℕ) (h : History Ω T n) :
    klDiv (referenceKernel A σ n h) (trueKernel A σ n h) ≤
      ENNReal.ofReal (‖hidden A n h‖ ^ 2 / (2 * σ ^ 2)) := by
  have heq := censored_innovation_klDiv_le (rowMap (A.original.rowProtocol.rows n h))
    (exposure A.original.rowProtocol.rows n h) (fittedMean A.original.rowProtocol.rows n h)
    (A.visible n h) (hidden A n h) hσ
  have hs : A.visible n h + hidden A n h =
      A.original.signal (ShiftedSequential.initialSeed n h) := by
    unfold hidden
    abel
  rw [hs] at heq
  simpa only [referenceKernel, trueKernel, observationKernel_apply, response, rowMap_apply] using heq

theorem conditionalCost_eq (A : CensoredProtocol Ω d T) {σ : ℝ} (hσ : σ ≠ 0) :
    SeededKernelKL.conditionalCost (referenceKernel A σ) (trueKernel A σ) = energyCost A σ := by
  funext n h
  simp only [SeededKernelKL.conditionalCost, conditional_klDiv A hσ,
    ENNReal.toReal_ofReal (energyCost_nonneg A σ n h)]

def referenceLaw (A : CensoredProtocol Ω d T) (σ : ℝ) (ν₀ : Measure Ω) (n : ℕ) :
    Measure (History Ω T n) := SeededKernelKL.transcriptLaw (referenceKernel A σ) ν₀ n

def trueLaw (A : CensoredProtocol Ω d T) (σ : ℝ) (ν₀ : Measure Ω) (n : ℕ) :
    Measure (History Ω T n) := SeededKernelKL.transcriptLaw (trueKernel A σ) ν₀ n

instance referenceLaw_probability (A : CensoredProtocol Ω d T) (σ : ℝ)
    (ν₀ : Measure Ω) [IsProbabilityMeasure ν₀] (n : ℕ) :
    IsProbabilityMeasure (referenceLaw A σ ν₀ n) := inferInstanceAs
      (IsProbabilityMeasure (SeededKernelKL.transcriptLaw (referenceKernel A σ) ν₀ n))

instance trueLaw_probability (A : CensoredProtocol Ω d T) (σ : ℝ)
    (ν₀ : Measure Ω) [IsProbabilityMeasure ν₀] (n : ℕ) :
    IsProbabilityMeasure (trueLaw A σ ν₀ n) := inferInstanceAs
      (IsProbabilityMeasure (SeededKernelKL.transcriptLaw (trueKernel A σ) ν₀ n))

theorem cumulativeCost_integrable (A : CensoredProtocol Ω d T) {σ : ℝ} (hσ : σ ≠ 0)
    (ν₀ : Measure Ω) [IsProbabilityMeasure ν₀] (C : ℕ → ℝ≥0)
    (hc : ∀ n h, ‖hidden A n h‖ ^ 2 / (2 * σ ^ 2) ≤ C n) (n : ℕ) :
    Integrable (SeededKernelKL.cumulativeCost (energyCost A σ) n) (referenceLaw A σ ν₀ n) := by
  have hb (k : ℕ) (h : History Ω T k) :
      klDiv (referenceKernel A σ k h) (trueKernel A σ k h) ≤ ENNReal.ofReal (C k) :=
    (conditional_klDiv_le A hσ k h).trans (ENNReal.ofReal_le_ofReal (hc k h))
  rw [← conditionalCost_eq A hσ]
  exact SeededKernelKL.cumulativeCost_integrable (referenceKernel A σ) ν₀ _
    (SeededKernelKL.conditionalCost_integrable (referenceKernel A σ) (trueKernel A σ) ν₀ C hb) n

theorem true_response (A : CensoredProtocol Ω d T) (σ : ℝ) (n : ℕ)
    (p : History Ω T n × Vec d) :
    response A σ n (fun h => A.original.signal (ShiftedSequential.initialSeed n h)) p =
      rowResponse (A.original.rowProtocol.rows n p.1) (ShiftedSequential.latent A.original σ n p) := by
  simp only [response, ShiftedSequential.latent, ShiftedSequential.posteriorMean, map_add, map_smul]
  rw [add_assoc]

theorem trueLaw_eq_fresh (A : CensoredProtocol Ω d T) (σ : ℝ)
    (ν₀ : Measure Ω) [IsProbabilityMeasure ν₀] (n : ℕ) :
    trueLaw A σ ν₀ n = ShiftedSequential.freshHistoryLaw A.original σ ν₀ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change trueLaw A σ ν₀ n ⊗ₘ trueKernel A σ n = _
      rw [ih, trueKernel, observationKernel_compProd, ShiftedSequential.freshHistoryLaw]
      congr 1
      funext p
      rw [true_response]
      rfl

/-- The comparison's true transcript is the marginal of the genuine static
signal-plus-Gaussian experiment, not an assumed posterior model. -/
theorem trueLaw_eq_static (A : CensoredProtocol Ω d T) (σ : ℝ)
    (ν₀ : Measure Ω) [IsProbabilityMeasure ν₀] (n : ℕ) :
    trueLaw A σ ν₀ n = (ShiftedSequential.staticJointLaw A.original σ ν₀ n).map Prod.fst := by
  rw [trueLaw_eq_fresh, ShiftedSequential.static_history_law]

/-- Exact adaptive KL is the expected sum of the genuine innovation energies.
Finite hidden-signal bounds are used solely to derive integrability. -/
theorem transcript_klDiv (A : CensoredProtocol Ω d T) {σ : ℝ} (hσ : σ ≠ 0)
    (ν₀ : Measure Ω) [IsProbabilityMeasure ν₀] (C : ℕ → ℝ≥0)
    (hc : ∀ n h, ‖hidden A n h‖ ^ 2 / (2 * σ ^ 2) ≤ C n) (n : ℕ) :
    klDiv (referenceLaw A σ ν₀ n) (trueLaw A σ ν₀ n) =
      ENNReal.ofReal (∫ h, SeededKernelKL.cumulativeCost (energyCost A σ) n h
        ∂referenceLaw A σ ν₀ n) := by
  have hb (k : ℕ) (h : History Ω T k) :
      klDiv (referenceKernel A σ k h) (trueKernel A σ k h) ≤ ENNReal.ofReal (C k) :=
    (conditional_klDiv_le A hσ k h).trans (ENNReal.ofReal_le_ofReal (hc k h))
  have heq : SeededKernelKL.conditionalCost (referenceKernel A σ) (trueKernel A σ) =
      energyCost A σ := by
    funext k h
    simp only [SeededKernelKL.conditionalCost, conditional_klDiv A hσ,
      ENNReal.toReal_ofReal (energyCost_nonneg A σ k h)]
  exact (SeededKernelKL.transcriptLaw_klDiv_eq_integral
    (referenceKernel A σ) (trueKernel A σ) ν₀ C hb n).trans (by rw [heq]; rfl)

theorem transcript_klDiv_le (A : CensoredProtocol Ω d T) {σ : ℝ} (hσ : σ ≠ 0)
    (ν₀ : Measure Ω) [IsProbabilityMeasure ν₀] (C : ℕ → ℝ≥0)
    (hc : ∀ n h, ‖hidden A n h‖ ^ 2 / (2 * σ ^ 2) ≤ C n)
    (n : ℕ) (cap : ℝ)
    (hcap : ∀ h, SeededKernelKL.cumulativeCost (energyCost A σ) n h ≤ cap) :
    klDiv (referenceLaw A σ ν₀ n) (trueLaw A σ ν₀ n) ≤ ENNReal.ofReal cap := by
  have hb (k : ℕ) (h : History Ω T k) :
      klDiv (referenceKernel A σ k h) (trueKernel A σ k h) ≤ ENNReal.ofReal (C k) :=
    (conditional_klDiv_le A hσ k h).trans (ENNReal.ofReal_le_ofReal (hc k h))
  have heq : SeededKernelKL.conditionalCost (referenceKernel A σ) (trueKernel A σ) =
      energyCost A σ := by
    funext k h
    simp only [SeededKernelKL.conditionalCost, conditional_klDiv A hσ,
      ENNReal.toReal_ofReal (energyCost_nonneg A σ k h)]
  apply SeededKernelKL.transcriptLaw_klDiv_le_cumulative
    (referenceKernel A σ) (trueKernel A σ) ν₀ C hb n cap
  simpa only [heq] using hcap

end MatchingBounds1005.CensoredGaussianProcess
