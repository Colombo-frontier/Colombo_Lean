import GradientHessian.ControllerRepairEvents
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! The actual chronological repair charge is dominated by its public
per-action event sum. Integrating this finite sum needs no independence
between actions. Bounds for each stopped repair event remain separate. -/

noncomputable section
namespace GradientHessian.ControllerRepairProbability
open Classical MeasureTheory TaskState TaskSlots ComparisonController
  ComparisonControllerLedger ControllerRepairEvents

variable {Ω X A : Type*} [MeasurableSpace Ω] [Fintype A]
variable {L M ell : ℕ}

def event (R : Ω → Rules L M ell X A) (ps : Ω → List (Pending X))
    (s : Ω → State L M ell) (a : A) : Set Ω :=
  {w | a ∈ actions (R w) (ps w) (s w)}

def count (R : Ω → Rules L M ell X A) (ps : Ω → List (Pending X))
    (s : Ω → State L M ell) (w : Ω) : ℕ :=
  tally (R w) (repairs (R w)) (ps w) (s w)

omit [MeasurableSpace Ω] in
theorem count_le_event_sum (R : Ω → Rules L M ell X A) (ps : Ω → List (Pending X))
    (s : Ω → State L M ell) (hs : ∀ w, Ready (s w)) (hell : 0<ell)
    (cost : A → ℕ) (hcost : ∀ w a, actionCost (R w) a ≤ cost a) (w : Ω) :
    (count R ps s w : ℝ) ≤
      ∑ a : A, (event R ps s a).indicator (fun _ => (cost a : ℝ)) w := by
  have hb := total_charge_le_public_sum (R w) (ps w) (hs w) hell cost (hcost w)
  have hr := Nat.cast_le (α := ℝ).mpr hb
  simpa only [count,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,event,Set.indicator_apply,
    Set.mem_setOf_eq] using hr

theorem count_integrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (R : Ω → Rules L M ell X A) (ps : Ω → List (Pending X))
    (s : Ω → State L M ell) (hs : ∀ w, Ready (s w)) (hell : 0<ell)
    (cost : A → ℕ) (hcost : ∀ w a, actionCost (R w) a ≤ cost a)
    (hmeas : Measurable (count R ps s)) (hevent : ∀ a, MeasurableSet (event R ps s a)) :
    Integrable (fun w => (count R ps s w : ℝ)) μ := by
  have hi : ∀ a : A, Integrable ((event R ps s a).indicator (fun _ => (cost a : ℝ))) μ :=
    fun a => (integrable_const _).indicator (hevent a)
  apply (integrable_finset_sum Finset.univ (fun a _ => hi a)).mono'
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hmeas).aestronglyMeasurable
  filter_upwards [] with w
  simpa only [Function.comp_apply,Real.norm_eq_abs,
    abs_of_nonneg (show (0:ℝ)≤(count R ps s w:ℝ) from Nat.cast_nonneg _)] using
    count_le_event_sum R ps s hs hell cost hcost w

/-- Exact event probabilities bound the mean actual repair charge. -/
theorem mean_le_event_sum (μ : Measure Ω) [IsFiniteMeasure μ]
    (R : Ω → Rules L M ell X A) (ps : Ω → List (Pending X))
    (s : Ω → State L M ell) (hs : ∀ w, Ready (s w)) (hell : 0<ell)
    (cost : A → ℕ) (hcost : ∀ w a, actionCost (R w) a ≤ cost a)
    (hmeas : Measurable (count R ps s)) (hevent : ∀ a, MeasurableSet (event R ps s a)) :
    (∫ w, (count R ps s w : ℝ) ∂μ) ≤ ∑ a : A, (cost a : ℝ)*μ.real (event R ps s a) := by
  have hi : ∀ a : A, Integrable ((event R ps s a).indicator (fun _ => (cost a : ℝ))) μ :=
    fun a => (integrable_const _).indicator (hevent a)
  calc
    _ ≤ ∫ w, ∑ a : A, (event R ps s a).indicator (fun _ => (cost a : ℝ)) w ∂μ :=
      integral_mono (count_integrable μ R ps s hs hell cost hcost hmeas hevent)
        (integrable_finset_sum Finset.univ (fun a _ => hi a))
        (count_le_event_sum R ps s hs hell cost hcost)
    _ = _ := by
      rw [integral_finset_sum Finset.univ (fun a _ => hi a)]
      apply Finset.sum_congr rfl
      intro a _
      rw [integral_indicator_const _ (hevent a)]
      simp only [smul_eq_mul,mul_comm]

theorem mean_le_probability_bounds (μ : Measure Ω) [IsFiniteMeasure μ]
    (R : Ω → Rules L M ell X A) (ps : Ω → List (Pending X))
    (s : Ω → State L M ell) (hs : ∀ w, Ready (s w)) (hell : 0<ell)
    (cost : A → ℕ) (hcost : ∀ w a, actionCost (R w) a ≤ cost a)
    (hmeas : Measurable (count R ps s)) (hevent : ∀ a, MeasurableSet (event R ps s a))
    (p : A → ℝ) (hp : ∀ a, μ.real (event R ps s a) ≤ p a) :
    (∫ w, (count R ps s w : ℝ) ∂μ) ≤ ∑ a : A, (cost a : ℝ)*p a := by
  refine (mean_le_event_sum μ R ps s hs hell cost hcost hmeas hevent).trans
    (Finset.sum_le_sum ?_)
  intro a _
  exact mul_le_mul_of_nonneg_left (hp a) (Nat.cast_nonneg _)

end GradientHessian.ControllerRepairProbability
