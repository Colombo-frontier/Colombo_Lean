import MatchingBounds1005.ShiftedPosterior

/-!
# Static signal-plus-Gaussian posterior for finite adaptive transcripts

The initial signal is a measurable function of the independent seed. The
static experiment retains `signal(seed) + σ Z` unchanged. The posterior
factorization is derived by finite induction, including the unobserved part
of that original signal at every step.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal NNReal

namespace MatchingBounds1005.ShiftedSequential
open GaussianVector AdaptiveGaussian GaussianFitter PosteriorGaussian
open SequentialPosterior ShiftedPosterior

variable {Ω : Type*} [MeasurableSpace Ω] {d T : ℕ}

def initialSeed : (n : ℕ) → History Ω T n → Ω
  | 0, h => h
  | n + 1, h => initialSeed n h.1

theorem initialSeed_measurable (n : ℕ) : Measurable (initialSeed (Ω := Ω) (T := T) n) := by
  induction n with
  | zero => exact measurable_id
  | succ n ih => exact ih.comp measurable_fst

structure ShiftedProtocol (Ω : Type*) [MeasurableSpace Ω] (d T : ℕ) where
  rowProtocol : RowProtocol Ω d T
  signal : Ω → Vec d
  measurable_signal : Measurable signal

def posteriorMean (A : ShiftedProtocol Ω d T) (n : ℕ) (h : History Ω T n) : Vec d :=
  fittedMean A.rowProtocol.rows n h + projection (exposure A.rowProtocol.rows n h)ᗮ
    (A.signal (initialSeed n h))

attribute [local irreducible] projection fitter Submodule.span

theorem posteriorMean_measurable (A : ShiftedProtocol Ω d T) (n : ℕ) :
    Measurable (posteriorMean A n) :=
  (measurable_fittedMean A.rowProtocol n).add
    ((measurable_complement (exposure A.rowProtocol.rows n) (measurable_exposure A.rowProtocol n)).comp
      (measurable_id.prodMk (A.measurable_signal.comp (initialSeed_measurable n))))

theorem residual_posteriorMean (A : ShiftedProtocol Ω d T) (n : ℕ) (h : History Ω T n) :
    projection (Submodule.span ℝ (Set.range (A.rowProtocol.rows n h)))ᗮ (posteriorMean A n h) =
      projection (Submodule.span ℝ (Set.range (A.rowProtocol.rows n h)))ᗮ
        (A.signal (initialSeed n h)) := by
  let V := exposure A.rowProtocol.rows n h
  let K := Submodule.span ℝ (Set.range (A.rowProtocol.rows n h))
  have hVK : V ≤ K := A.rowProtocol.nested n h
  have hm : fittedMean A.rowProtocol.rows n h ∈ K :=
    hVK (fittedMean_mem A.rowProtocol n h)
  change projection Kᗮ (fittedMean A.rowProtocol.rows n h + projection Vᗮ _) = _
  rw [map_add, projection_orthogonal_eq_sub K (fittedMean A.rowProtocol.rows n h),
    projection_of_mem K _ hm, sub_self, zero_add,
    projection_small_large Kᗮ Vᗮ (Submodule.orthogonal_le hVK)]

theorem mean_update (A : ShiftedProtocol Ω d T) (n : ℕ) (p : History Ω T (n + 1)) :
    fitter (A.rowProtocol.rows n p.1) p.2 +
      projection (Submodule.span ℝ (Set.range (A.rowProtocol.rows n p.1)))ᗮ (posteriorMean A n p.1) =
        posteriorMean A (n + 1) p := by
  rw [residual_posteriorMean]
  rfl

def latent (A : ShiftedProtocol Ω d T) (σ : ℝ) (n : ℕ) (p : History Ω T n × Vec d) : Vec d :=
  posteriorMean A n p.1 + σ • projection (exposure A.rowProtocol.rows n p.1)ᗮ p.2

theorem latent_measurable (A : ShiftedProtocol Ω d T) (σ : ℝ) (n : ℕ) :
    Measurable (latent A σ n) :=
  ((posteriorMean_measurable A n).comp measurable_fst).add
    (measurable_const.smul (measurable_complement (exposure A.rowProtocol.rows n)
      (measurable_exposure A.rowProtocol n)))

def observe (A : ShiftedProtocol Ω d T) (σ : ℝ) (n : ℕ)
    (p : History Ω T n × Vec d) : History Ω T (n + 1) :=
  (p.1, rowResponse (A.rowProtocol.rows n p.1) (latent A σ n p))

theorem observe_measurable (A : ShiftedProtocol Ω d T) (σ : ℝ) (n : ℕ) :
    Measurable (observe A σ n) :=
  measurable_fst.prodMk
    ((measurable_rowResponse_family (A.rowProtocol.rows n) (A.rowProtocol.measurable_rows n)).comp
      (measurable_fst.prodMk (latent_measurable A σ n)))

def freshHistoryLaw (A : ShiftedProtocol Ω d T) (σ : ℝ) (ν₀ : Measure Ω) :
    (n : ℕ) → Measure (History Ω T n)
  | 0 => ν₀
  | n + 1 => ((freshHistoryLaw A σ ν₀ n).prod (standardGaussian d)).map (observe A σ n)

instance freshHistoryLaw_probability (A : ShiftedProtocol Ω d T) (σ : ℝ)
    (ν₀ : Measure Ω) [IsProbabilityMeasure ν₀] (n : ℕ) :
    IsProbabilityMeasure (freshHistoryLaw A σ ν₀ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure ν₀)
  | succ n ih =>
      letI := ih
      exact isProbabilityMeasure_map (observe_measurable A σ n).aemeasurable

def representedLaw (A : ShiftedProtocol Ω d T) (σ : ℝ) (ν₀ : Measure Ω) (n : ℕ) :
    Measure (History Ω T n × Vec d) :=
  ((freshHistoryLaw A σ ν₀ n).prod (standardGaussian d)).map (fun p => (p.1, latent A σ n p))

/-- The parameter is drawn once from the explicit shifted Gaussian prior
and is then copied unchanged at every adaptive observation. -/
def staticJointLaw (A : ShiftedProtocol Ω d T) (σ : ℝ) (ν₀ : Measure Ω) :
    (n : ℕ) → Measure (History Ω T n × Vec d)
  | 0 => (ν₀.prod (standardGaussian d)).map (fun p => (p.1, A.signal p.1 + σ • p.2))
  | n + 1 => (staticJointLaw A σ ν₀ n).map (staticUpdate A.rowProtocol n)

theorem latent_zero (A : ShiftedProtocol Ω d T) (σ : ℝ) (p : Ω × Vec d) :
    latent A σ 0 p = A.signal p.1 + σ • p.2 := by
  have hp (x : Vec d) : projection (⊤ : Submodule ℝ (Vec d)) x = x :=
    projection_of_mem _ _ trivial
  simp only [latent, posteriorMean, fittedMean, exposure, initialSeed,
    Submodule.bot_orthogonal_eq_top, hp, zero_add]

/-- Actual finite posterior factorization for the manuscript's signal-plus-
Gaussian static parameter. No posterior law occurs among the assumptions. -/
theorem staticJointLaw_eq_represented (A : ShiftedProtocol Ω d T) (σ : ℝ)
    (ν₀ : Measure Ω) [IsProbabilityMeasure ν₀] (n : ℕ) :
    staticJointLaw A σ ν₀ n = representedLaw A σ ν₀ n := by
  induction n with
  | zero =>
      rw [staticJointLaw, representedLaw, freshHistoryLaw]
      simp only [latent_zero]
      rfl
  | succ n ih =>
      rw [staticJointLaw, ih, representedLaw,
        Measure.map_map (measurable_staticUpdate A.rowProtocol n)
          (measurable_fst.prodMk (latent_measurable A σ n))]
      have hp := shifted_step_factorization (freshHistoryLaw A σ ν₀ n)
        (exposure A.rowProtocol.rows n) (measurable_exposure A.rowProtocol n)
        (A.rowProtocol.rows n) (A.rowProtocol.measurable_rows n) (A.rowProtocol.nested n)
        (posteriorMean A n) (posteriorMean_measurable A n) σ
      simpa only [staticUpdate, representedLaw, freshHistoryLaw, observe, latent,
        mean_update, exposure, Function.comp_def] using hp

theorem static_history_law (A : ShiftedProtocol Ω d T) (σ : ℝ)
    (ν₀ : Measure Ω) [IsProbabilityMeasure ν₀] (n : ℕ) :
    (staticJointLaw A σ ν₀ n).map Prod.fst = freshHistoryLaw A σ ν₀ n := by
  rw [staticJointLaw_eq_represented, representedLaw,
    Measure.map_map measurable_fst (measurable_fst.prodMk (latent_measurable A σ n))]
  change (((freshHistoryLaw A σ ν₀ n).prod (standardGaussian d)).map Prod.fst) = _
  simp

end MatchingBounds1005.ShiftedSequential
