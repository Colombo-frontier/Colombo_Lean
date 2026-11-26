import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Hidden-component counting with a private randomized seed

The sets `A j` and `B j` are actual measurable success events.  The only
indistinguishability premise says that, for an unqueried hidden component,
the two success events cannot both occur.  The visited set is allowed to
depend arbitrarily on the seed and need not itself be measurable.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace NCConcave16991.BaselineCounting

noncomputable section

def score (P : Prop) : ℝ := by classical exact if P then 1 else 0

theorem score_pair_le {P Q : Prop} (h : ¬(P ∧ Q)) : score P + score Q ≤ 1 := by
  classical
  by_cases hp : P <;> by_cases hq : Q <;> simp [score, hp, hq] at *

/-- A seedwise count; no distributional or independence assumptions enter. -/
theorem pointwise_bound {n : ℕ} (Q : Finset (Fin n)) (A B : Fin n → Prop)
    (h : ∀ j, j ∉ Q → ¬ (A j ∧ B j)) :
    ∑ j, (score (A j) + score (B j)) ≤ (n:ℝ) + Q.card := by
  classical
  have hj (j : Fin n) : score (A j) + score (B j) ≤
      1 + if j ∈ Q then (1:ℝ) else 0 := by
    by_cases hq : j ∈ Q
    · simp only [hq, ite_true]
      unfold score
      split_ifs <;> norm_num
    · simpa only [hq, ite_false, add_zero] using score_pair_le (h j hq)
  calc
    _ ≤ ∑ j, (1 + if j ∈ Q then (1:ℝ) else 0) := Finset.sum_le_sum (fun j _ ↦ hj j)
    _ = (n:ℝ) + Q.card := by
      rw [Finset.sum_add_distrib]
      simp

theorem pointwise_budget_bound {n T : ℕ} (Q : Finset (Fin n)) (A B : Fin n → Prop)
    (hQ : Q.card ≤ T) (h : ∀ j, j ∉ Q → ¬ (A j ∧ B j)) :
    ∑ j, (score (A j) + score (B j)) ≤ (n:ℝ) + T :=
  (pointwise_bound Q A B h).trans (add_le_add (le_refl _) (Nat.cast_le.mpr hQ))

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem score_integrable {A : Set Ω} (hA : MeasurableSet A) :
    Integrable (fun s ↦ score (s ∈ A)) μ := by
  classical
  have he : (fun s ↦ score (s ∈ A)) = A.indicator (fun _ ↦ (1 : ℝ)) := by
    funext s
    simp [score, Set.indicator]
  rw [he]
  exact (integrable_const (μ := μ) (1 : ℝ)).indicator hA

theorem integral_score {A : Set Ω} (hA : MeasurableSet A) :
    ∫ s, score (s ∈ A) ∂μ = μ.real A := by
  classical
  simpa only [score, Set.indicator_apply, Pi.one_apply] using
    (integral_indicator_one (μ := μ) hA)

/-- Integrating the exact seedwise count gives a sum of actual probabilities. -/
theorem probability_sum_bound {n T : ℕ} (A B : Fin n → Set Ω)
    (hA : ∀ j, MeasurableSet (A j)) (hB : ∀ j, MeasurableSet (B j))
    (Q : Ω → Finset (Fin n)) (hQ : ∀ s, (Q s).card ≤ T)
    (hind : ∀ s j, j ∉ Q s → ¬ (s ∈ A j ∧ s ∈ B j)) :
    ∑ j, (μ.real (A j) + μ.real (B j)) ≤ (n:ℝ) + T := by
  have hi (j : Fin n) : Integrable (fun s ↦ score (s ∈ A j) + score (s ∈ B j)) μ :=
    (score_integrable μ (hA j)).add (score_integrable μ (hB j))
  have hs : Integrable (fun s ↦ ∑ j, (score (s ∈ A j) + score (s ∈ B j))) μ :=
    integrable_finsetSum _ (fun j _ ↦ hi j)
  have hb := integral_mono hs (integrable_const ((n:ℝ)+T))
    (fun s ↦ pointwise_budget_bound (Q s) (fun j ↦ s ∈ A j) (fun j ↦ s ∈ B j)
      (hQ s) (hind s))
  rw [integral_finsetSum _ (fun j _ ↦ hi j)] at hb
  simp only [integral_add (score_integrable μ (hA _)) (score_integrable μ (hB _)),
    integral_score μ (hA _), integral_score μ (hB _), integral_const,
    probReal_univ, smul_eq_mul, one_mul] at hb
  exact hb

theorem success_probability_real {A : Set Ω} (h : (2/3:ℝ≥0∞) ≤ μ A) :
    (2/3:ℝ) ≤ μ.real A := by
  have hh := ENNReal.toReal_mono (measure_ne_top μ A) h
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_ofNat] at hh
  exact hh

/-- The quantitative randomized lower bound: every budget succeeds on all
`2n` instances with probability at least `2/3` only if `T ≥ n/3`. -/
theorem randomized_budget_lower {n T : ℕ} (A B : Fin n → Set Ω)
    (hA : ∀ j, MeasurableSet (A j)) (hB : ∀ j, MeasurableSet (B j))
    (hpA : ∀ j, (2/3:ℝ≥0∞) ≤ μ (A j)) (hpB : ∀ j, (2/3:ℝ≥0∞) ≤ μ (B j))
    (Q : Ω → Finset (Fin n)) (hQ : ∀ s, (Q s).card ≤ T)
    (hind : ∀ s j, j ∉ Q s → ¬ (s ∈ A j ∧ s ∈ B j)) :
    (n:ℝ)/3 ≤ T := by
  have hs := probability_sum_bound μ A B hA hB Q hQ hind
  have hl : (n:ℝ)*(4/3:ℝ) ≤ ∑ j, (μ.real (A j)+μ.real (B j)) := by
    calc
      _ = ∑ _j : Fin n, (4/3:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j _ ↦ by
        have ha := success_probability_real μ (hpA j)
        have hb := success_probability_real μ (hpB j)
        linarith)
  linarith

end

end NCConcave16991.BaselineCounting
