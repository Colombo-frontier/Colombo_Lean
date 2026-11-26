import MatchingBounds1005.ReferenceTransition

/-!
# The accessible transition is exactly the proved reference kernel

This identifies the deterministic finite-row implementation with the actual
censored Gaussian response used in the KL theorem, including the empty
initial history. No reference-law equivalence is assumed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace MatchingBounds1005.ReferenceTransitionLink
open GaussianVector GaussianFitter AdaptiveGaussian PosteriorGaussian SequentialPosterior
open CensoredGaussianProcess ReferenceTransition

variable {Ω : Type*} [MeasurableSpace Ω] {d T : ℕ}

def oldRows (rows : (n : ℕ) → History Ω T n → Fin T → Vec d) :
    (n : ℕ) → History Ω T n → Fin T → Vec d
  | 0, _ => 0
  | n + 1, h => rows n h.1

def oldAnswers : (n : ℕ) → History Ω T n → Fin T → ℝ
  | 0, _ => 0
  | _n + 1, h => h.2

theorem oldRows_span (rows : (n : ℕ) → History Ω T n → Fin T → Vec d)
    (n : ℕ) (h : History Ω T n) :
    Submodule.span ℝ (Set.range (oldRows rows n h)) = exposure rows n h := by
  cases n with
  | zero =>
      apply Submodule.span_eq_bot.mpr
      rintro _ ⟨i, rfl⟩
      rfl
  | succ n => rfl

theorem oldRows_fitter (rows : (n : ℕ) → History Ω T n → Fin T → Vec d)
    (n : ℕ) (h : History Ω T n) :
    fitter (oldRows rows n h) (oldAnswers n h) = fittedMean rows n h := by
  cases n with
  | zero =>
      have hz : rowResponse (oldRows rows 0 h) (0 : Vec d) = (0 : Fin T → ℝ) := by
        funext i
        simp only [rowResponse, inner_zero_right, Pi.zero_apply]
      change fitter (oldRows rows 0 h) 0 = 0
      rw [← hz, fitter_response_projection, map_zero]
  | succ n => rfl

def accessibleInput (A : CensoredProtocol Ω d T) (n : ℕ) (h : History Ω T n) : Input d T :=
  ((oldRows A.original.rowProtocol.rows n h, oldAnswers n h),
    (A.original.rowProtocol.rows n h, A.visible n h))

theorem accessibleInput_measurable (A : CensoredProtocol Ω d T) (n : ℕ) :
    Measurable (accessibleInput A n) := by
  have hr : Measurable (fun h => oldRows A.original.rowProtocol.rows n h) := by
    cases n with
    | zero => exact measurable_const
    | succ n =>
        exact (measurable_pi_lambda _ (A.original.rowProtocol.measurable_rows n)).comp measurable_fst
  have hy : Measurable (oldAnswers (Ω := Ω) (T := T) n) := by
    cases n with
    | zero => exact measurable_const
    | succ n => exact measurable_snd
  exact (hr.prodMk hy).prodMk
    ((measurable_pi_lambda _ (A.original.rowProtocol.measurable_rows n)).prodMk (A.measurable_visible n))

attribute [local irreducible] projection fitter rowResponse Submodule.span Submodule.orthogonal

theorem transition_eq_response (A : CensoredProtocol Ω d T) (σ : ℝ) (n : ℕ)
    (h : History Ω T n) (z : Vec d) :
    transition σ (accessibleInput A n h, z) = response A σ n (A.visible n) (h, z) := by
  unfold transition accessibleInput response
  dsimp only
  rw [oldRows_fitter, oldRows_span]

/-- The actual Gaussian reference kernel is implemented by the accessible
finite-row transition with one independent private Gaussian input. -/
theorem referenceKernel_eq_transition (A : CensoredProtocol Ω d T) (σ : ℝ) (n : ℕ)
    (h : History Ω T n) :
    referenceKernel A σ n h = (standardGaussian d).map (fun z => transition σ (accessibleInput A n h, z)) := by
  simp only [transition_eq_response]
  rfl

end MatchingBounds1005.ReferenceTransitionLink
