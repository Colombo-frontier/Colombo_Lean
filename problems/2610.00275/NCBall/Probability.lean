import NCBall.Scaling
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real

/-!
# Honest probability interfaces for the final lower-bound reduction

The union bound and extraction of a fixed hard instance are proved here for
actual measures and integrals. The one-query early-hit estimate is an explicit
hypothesis, not a proved Gaussian theorem.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace NCBall

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- N evaluations plus the output contribute N+1 possible first hits. -/
theorem first_hit_union_bound {N : ℕ} (hit : Fin (N + 1) → Set Ω) {p : ℝ}
    (h : ∀ i, μ.real (hit i) ≤ p) :
    μ.real (⋃ i, hit i) ≤ ((N : ℝ) + 1) * p := by
  calc
    μ.real (⋃ i, hit i) ≤ ∑ i, μ.real (hit i) := measureReal_iUnion_fintype_le hit
    _ ≤ ∑ _i : Fin (N + 1), p := Finset.sum_le_sum fun i _ => h i
    _ = ((N : ℝ) + 1) * p := by simp

/-- Only success on good instances must be contained in the early-hit event.
This avoids applying the class-verification lemma to unbounded Gaussian draws. -/
theorem success_on_good_le {N : ℕ} (hit : Fin (N + 1) → Set Ω)
    (success good : Set Ω) {p : ℝ}
    (hcontain : success ∩ good ⊆ ⋃ i, hit i)
    (hhit : ∀ i, μ.real (hit i) ≤ p) :
    μ.real (success ∩ good) ≤ ((N : ℝ) + 1) * p :=
  (measureReal_mono hcontain).trans (first_hit_union_bound μ hit hhit)

omit [IsProbabilityMeasure μ] in
theorem conditional_success_lt_half (success good : Set Ω)
    (hgood : 7 / 8 ≤ μ.real good)
    (hsuccess : μ.real (success ∩ good) ≤ 1 / 4) :
    μ.real (success ∩ good) / μ.real good < 1 / 2 :=
  (conditioning_constants hgood hsuccess).2

/-- An average success mass ≤1/4 and good mass ≥7/8 imply that some fixed
good instance has success probability below 1/2. Here `p u` is the algorithm's
success probability on the fixed instance `u`. -/
theorem exists_hard_instance (good : Set Ω) (hgood : MeasurableSet good)
    (p : Ω → ℝ) (hp : IntegrableOn p good μ)
    (hmass : 7 / 8 ≤ μ.real good) (haverage : ∫ u in good, p u ∂μ ≤ 1 / 4) :
    ∃ u ∈ good, p u < 1 / 2 := by
  by_contra h
  push_neg at h
  have hc : IntegrableOn (fun _ : Ω => (1 / 2 : ℝ)) good μ :=
    integrableOn_const.mpr (Or.inr (measure_lt_top μ good))
  have hint := setIntegral_mono_on hc hp hgood h
  rw [setIntegral_const, smul_eq_mul] at hint
  linarith

end NCBall
