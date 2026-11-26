import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-!
# Verified amplification with actual independent product seeds

`bestCandidate` selects a candidate of minimum verified residual, retaining
the first candidate on ties. Its measurability is proved. Independent runs
use the finite product of the original seed measure; the power law is proved
from the product measure, not postulated as an independence assumption.
-/

namespace Matvec

open MeasureTheory

noncomputable section

variable {E Seed : Type*}

/-- A measurable finite minimum selector; R denotes the number of candidates
after the first, so there are R+1 candidates. -/
def bestCandidate (score : E → ℝ) : (R : ℕ) → (Fin (R + 1) → E) → E
  | 0, c => c 0
  | R + 1, c =>
      let tail := bestCandidate score R (fun i => c i.succ)
      if score (c 0) ≤ score tail then c 0 else tail

theorem bestCandidate_mem (score : E → ℝ) (R : ℕ) (c : Fin (R + 1) → E) :
    ∃ i, bestCandidate score R c = c i := by
  induction R with
  | zero => exact ⟨0, rfl⟩
  | succ R ih =>
    simp only [bestCandidate]
    split
    · exact ⟨0, rfl⟩
    · obtain ⟨i, hi⟩ := ih (fun i => c i.succ)
      exact ⟨i.succ, hi⟩

theorem bestCandidate_score_le (score : E → ℝ) (R : ℕ)
    (c : Fin (R + 1) → E) (i : Fin (R + 1)) :
    score (bestCandidate score R c) ≤ score (c i) := by
  induction R with
  | zero => have hi : i = 0 := Fin.ext (by omega); subst i; exact le_rfl
  | succ R ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [bestCandidate]
      split
      · exact le_rfl
      · exact (le_of_not_ge ‹¬_›)
    · simp only [bestCandidate]
      split
      · exact le_trans ‹_ ≤ _› (ih (fun i => c i.succ) i)
      · exact ih (fun i => c i.succ) i

theorem bestCandidate_failure_iff (score : E → ℝ) (R : ℕ)
    (c : Fin (R + 1) → E) (δ : ℝ) :
    δ < score (bestCandidate score R c) ↔ ∀ i, δ < score (c i) := by
  constructor
  · intro h i
    exact h.trans_le (bestCandidate_score_le score R c i)
  · intro h
    obtain ⟨i, hi⟩ := bestCandidate_mem score R c
    rw [hi]
    exact h i

theorem bestCandidate_success (score : E → ℝ) (R : ℕ)
    (c : Fin (R + 1) → E) (δ : ℝ) (h : ∃ i, score (c i) ≤ δ) :
    score (bestCandidate score R c) ≤ δ := by
  obtain ⟨i, hi⟩ := h
  exact (bestCandidate_score_le score R c i).trans hi

theorem measurable_bestCandidate [MeasurableSpace E] (score : E → ℝ)
    (hscore : Measurable score) (R : ℕ) : Measurable (bestCandidate score R) := by
  induction R with
  | zero => exact measurable_pi_apply 0
  | succ R ih =>
    have hhead : Measurable (fun c : Fin (R + 2) → E => c 0) := measurable_pi_apply 0
    have htail : Measurable (fun c : Fin (R + 2) → E =>
        bestCandidate score R (fun i => c i.succ)) :=
      ih.comp (measurable_pi_lambda _ fun i => measurable_pi_apply i.succ)
    exact hhead.piecewise (measurableSet_le (hscore.comp hhead) (hscore.comp htail)) htail

/-- R+1 independent base runs, followed by exact residual verification and
minimum selection. -/
def verifiedRepeat (score : E → ℝ) (candidate : Seed → E) (R : ℕ)
    (seeds : Fin (R + 1) → Seed) : E :=
  bestCandidate score R (fun i => candidate (seeds i))

theorem measurable_verifiedRepeat [MeasurableSpace Seed] [MeasurableSpace E]
    (score : E → ℝ) (candidate : Seed → E) (R : ℕ)
    (hscore : Measurable score) (hcandidate : Measurable candidate) :
    Measurable (verifiedRepeat score candidate R) :=
  (measurable_bestCandidate score hscore R).comp
    (measurable_pi_lambda _ fun i => hcandidate.comp (measurable_pi_apply i))

/-- Product-measure derivation of the all-failure probability, valid also for
zero repetitions. -/
theorem independent_all_failure [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (failure : Set Seed) (R : ℕ) :
    (Measure.pi (fun _ : Fin R => μ)).real {seeds | ∀ i, seeds i ∈ failure} =
      (μ.real failure) ^ R := by
  have hevent : {seeds : Fin R → Seed | ∀ i, seeds i ∈ failure} =
      Set.pi Set.univ (fun _ => failure) := by ext seeds; simp
  rw [hevent]
  simp only [Measure.real, Measure.pi_pi, Finset.prod_const, Finset.card_univ,
    ENNReal.toReal_pow, Fintype.card_fin]

/-- Exact failure probability of minimum-verified-residual amplification. -/
theorem verifiedRepeat_failure_probability [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (score : E → ℝ)
    (candidate : Seed → E) (R : ℕ) (δ : ℝ) :
    (Measure.pi (fun _ : Fin (R + 1) => μ)).real
      {seeds | δ < score (verifiedRepeat score candidate R seeds)} =
      (μ.real {seed | δ < score (candidate seed)}) ^ (R + 1) := by
  have hevent : {seeds : Fin (R + 1) → Seed |
      δ < score (verifiedRepeat score candidate R seeds)} =
      {seeds | ∀ i, seeds i ∈ {seed | δ < score (candidate seed)}} := by
    ext seeds
    exact bestCandidate_failure_iff score R (fun i => candidate (seeds i)) δ
  rw [hevent]
  exact independent_all_failure μ _ (R + 1)

/-- `lem:amplify`: base failure probability at most 2/5 becomes at most
(2/5)^(R+1) after R+1 genuinely independent runs. -/
theorem verified_amplification [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (score : E → ℝ)
    (candidate : Seed → E) (R : ℕ) (δ : ℝ)
    (hfail : μ.real {seed | δ < score (candidate seed)} ≤ 2 / 5) :
    (Measure.pi (fun _ : Fin (R + 1) => μ)).real
      {seeds | δ < score (verifiedRepeat score candidate R seeds)} ≤
      (2 / 5 : ℝ) ^ (R + 1) := by
  rw [verifiedRepeat_failure_probability]
  exact pow_le_pow_left₀ (measureReal_nonneg) hfail (R + 1)

/-- Success probability 3/5 yields the failure hypothesis used above. -/
theorem failure_le_two_fifths [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (score : Seed → ℝ)
    (hscore : Measurable score) (δ : ℝ)
    (hsuccess : 3 / 5 ≤ μ.real {seed | score seed ≤ δ}) :
    μ.real {seed | δ < score seed} ≤ 2 / 5 := by
  have hmeas : MeasurableSet {seed | score seed ≤ δ} := measurableSet_le hscore measurable_const
  have hcompl : {seed | δ < score seed} = {seed | score seed ≤ δ}ᶜ := by
    ext seed
    simp
  rw [hcompl, measureReal_compl hmeas, measureReal_univ_eq_one]
  linarith

/-- Full verified amplification for a measurable base solver and a
measurable residual score, starting from success probability at least 3/5. -/
theorem verified_amplification_of_success [MeasurableSpace Seed] [MeasurableSpace E]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (score : E → ℝ)
    (candidate : Seed → E) (hscore : Measurable score) (hcandidate : Measurable candidate)
    (R : ℕ) (δ : ℝ) (hsuccess : 3 / 5 ≤ μ.real {seed | score (candidate seed) ≤ δ}) :
    Measurable (verifiedRepeat score candidate R) ∧
    (Measure.pi (fun _ : Fin (R + 1) => μ)).real
      {seeds | δ < score (verifiedRepeat score candidate R seeds)} ≤
      (2 / 5 : ℝ) ^ (R + 1) := by
  refine ⟨measurable_verifiedRepeat score candidate R hscore hcandidate, ?_⟩
  apply verified_amplification
  exact failure_le_two_fifths μ (score ∘ candidate) (hscore.comp hcandidate) δ hsuccess

/-- Concrete source residual verification is measurable and evaluates the
source operator once per candidate. The selected vector is a real output of
one of the independently seeded base runs. -/
theorem verified_residual_solver [MeasurableSpace Seed]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (H : E →L[ℝ] E) (r : E)
    (candidate : Seed → E) (hcandidate : Measurable candidate) (R : ℕ)
    (hsuccess : 3 / 5 ≤ μ.real {seed | ‖H (candidate seed) - r‖ ≤ ‖r‖ / 2}) :
    Measurable (verifiedRepeat (fun x => ‖H x - r‖) candidate R) ∧
    (Measure.pi (fun _ : Fin (R + 1) => μ)).real
      {seeds | ‖r‖ / 2 < ‖H (verifiedRepeat (fun x => ‖H x - r‖) candidate R seeds) - r‖} ≤
      (2 / 5 : ℝ) ^ (R + 1) := by
  apply verified_amplification_of_success μ _ candidate _ hcandidate R (‖r‖ / 2) hsuccess
  exact (H.continuous.sub continuous_const).norm.measurable

/-- Each run costs at most K matvecs and its exact residual verification costs
one more. The bound is pointwise in every tuple of seeds. -/
theorem verified_amplification_cost (R K : ℕ) (cost : Seed → ℕ)
    (hcost : ∀ seed, cost seed ≤ K) (seeds : Fin R → Seed) :
    ∑ i, (cost (seeds i) + 1) ≤ R * (K + 1) := by
  calc
    _ ≤ ∑ _ : Fin R, (K + 1) := Finset.sum_le_sum (fun i _ => Nat.add_le_add_right (hcost _) 1)
    _ = _ := by simp

end
end Matvec
