import GradientHessian.Machine
import Mathlib.MeasureTheory.Measure.Prod

/-! Exact replay and fresh-parameter finite-list bounds.

Replay is proved for the actual mixed-query state recursion. The probability
bound uses a genuine product measure: the test list depends on the other raw
variables, while the tested parameter is independent. It never asserts
freshness after conditioning on previous misses.
-/

namespace GradientHessian.Shadow

open MeasureTheory Set
open scoped ENNReal

variable {Seed State X Y Z : Type*}
  [MeasurableSpace Seed] [MeasurableSpace State] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

theorem step_eq_of_reply_agreement (P : Machine.Policy Seed State X Y Z)
    (realOrdinary shadowOrdinary : X → Y) (realRich shadowRich : X → Z) (s : State)
    (ho : P.mode s = 2 → realOrdinary (P.point s) = shadowOrdinary (P.point s))
    (hr : P.mode s = 3 → realRich (P.point s) = shadowRich (P.point s)) :
    P.step realOrdinary realRich s = P.step shadowOrdinary shadowRich s := by
  unfold Machine.Policy.step
  split_ifs with h₀ h₁ h₂
  · rfl
  · rfl
  · rw [ho h₂]
  · have h₃ : P.mode s = 3 := by omega
    rw [hr h₃]

theorem run_eq_before_first_difference (P : Machine.Policy Seed State X Y Z)
    (realOrdinary shadowOrdinary : X → Y) (realRich shadowRich : X → Z)
    (seed : Seed) (N : ℕ)
    (hagree : ∀ i < N,
      let s := P.run shadowOrdinary shadowRich i seed
      (P.mode s = 2 → realOrdinary (P.point s) = shadowOrdinary (P.point s)) ∧
      (P.mode s = 3 → realRich (P.point s) = shadowRich (P.point s))) :
    ∀ n ≤ N, P.run realOrdinary realRich n seed = P.run shadowOrdinary shadowRich n seed := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    change P.step realOrdinary realRich (P.run realOrdinary realRich n seed) =
      P.step shadowOrdinary shadowRich (P.run shadowOrdinary shadowRich n seed)
    rw [ih (by omega)]
    exact step_eq_of_reply_agreement P _ _ _ _ _ (hagree n (by omega)).1
      (hagree n (by omega)).2

theorem first_difference_has_query_witness (P : Machine.Policy Seed State X Y Z)
    (realOrdinary shadowOrdinary : X → Y) (realRich shadowRich : X → Z)
    (seed : Seed) (N : ℕ)
    (hdiff : P.run realOrdinary realRich N seed ≠ P.run shadowOrdinary shadowRich N seed) :
    ∃ i < N,
      let s := P.run shadowOrdinary shadowRich i seed
      (P.mode s = 2 ∧ realOrdinary (P.point s) ≠ shadowOrdinary (P.point s)) ∨
      (P.mode s = 3 ∧ realRich (P.point s) ≠ shadowRich (P.point s)) := by
  classical
  by_contra h
  apply hdiff
  apply run_eq_before_first_difference P _ _ _ _ seed N _ N le_rfl
  intro i hi
  constructor
  · intro hm
    by_contra he
    exact h ⟨i, hi, Or.inl ⟨hm, he⟩⟩
  · intro hm
    by_contra he
    exact h ⟨i, hi, Or.inr ⟨hm, he⟩⟩

variable {Θ W : Type*} [MeasurableSpace Θ] [MeasurableSpace W]

omit [MeasurableSpace X] in
/-- A union bound on a fixed finite list, including an arbitrary output test. -/
theorem fixed_list_hit_bound (ν : Measure Θ) (hit : Θ → X → Prop)
    (N : ℕ) (queries : Fin N → X) (p : ℝ≥0∞)
    (hpoint : ∀ x, ν {θ | hit θ x} ≤ p) :
    ν {θ | ∃ i : Fin N, hit θ (queries i)} ≤ N * p := by
  have heq : {θ | ∃ i : Fin N, hit θ (queries i)} = ⋃ i : Fin N, {θ | hit θ (queries i)} := by
    ext θ; simp
  rw [heq]
  calc
    ν (⋃ i : Fin N, {θ | hit θ (queries i)}) ≤ ∑ i : Fin N, ν {θ | hit θ (queries i)} :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _ : Fin N, p := Finset.sum_le_sum fun i _ => hpoint (queries i)
    _ = N * p := by simp

omit [MeasurableSpace X] in
/-- Conditioning on all *other* raw variables is implemented by the sections
of the product law. The selected list can depend measurably on those variables;
it has no access to the independent target parameter. -/
theorem independent_list_hit_bound (μ : Measure W) (ν : Measure Θ)
    [IsProbabilityMeasure μ] [SFinite ν]
    (hit : Θ → X → Prop) (N : ℕ) (queries : W → Fin N → X) (p : ℝ≥0∞)
    (hpoint : ∀ x, ν {θ | hit θ x} ≤ p)
    (hmeas : MeasurableSet {z : W × Θ | ∃ i : Fin N, hit z.2 (queries z.1 i)}) :
    (μ.prod ν) {z : W × Θ | ∃ i : Fin N, hit z.2 (queries z.1 i)} ≤ N * p := by
  rw [Measure.prod_apply hmeas]
  calc
    (∫⁻ w, ν (Prod.mk w ⁻¹' {z : W × Θ | ∃ i : Fin N, hit z.2 (queries z.1 i)}) ∂μ)
        ≤ ∫⁻ _ : W, (N : ℝ≥0∞) * p ∂μ := by
      apply lintegral_mono
      intro w
      exact fixed_list_hit_bound ν hit N (queries w) p hpoint
    _ = N * p := by simp

end GradientHessian.Shadow
