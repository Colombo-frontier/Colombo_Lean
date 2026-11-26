import FullJet.UnobservedStages

open scoped BigOperators

namespace FullJet

/-- If an unaligned stage must be charged at least `r`, a small total budget
forces many stages to lie in the designated short-alignment events. -/
theorem short_alignment_count_of_budget {Ω : Type*} {T : ℕ} (A : Fin T → Set Ω)
    (x : Ω) (cost : Fin T → ℕ) (r N : ℕ) (hr : 0 < r)
    (hcost : ∑ j, cost j ≤ N) (hN : 2 * N ≤ r * T)
    (hshort : ∀ j, cost j < r → x ∈ A j) :
    (T : ℝ) / 2 ≤ finiteEventCount A x := by
  classical
  have hpoint (j : Fin T) : (r : ℝ) ≤ cost j + r * (A j).indicator (fun _ => (1 : ℝ)) x := by
    by_cases hj : x ∈ A j
    · simp only [Set.indicator_of_mem hj, mul_one]
      exact le_add_of_nonneg_left (Nat.cast_nonneg _)
    · have hslow : r ≤ cost j := le_of_not_gt (fun hlt => hj (hshort j hlt))
      simp only [Set.indicator_of_not_mem hj, mul_zero, add_zero]
      exact_mod_cast hslow
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin T))) => hpoint j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hs
  have hc : (∑ j, (cost j : ℝ)) ≤ N := by exact_mod_cast hcost
  have hN' : (2 : ℝ) * N ≤ r * T := by exact_mod_cast hN
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  change (T : ℝ) * r ≤ (∑ j, (cost j : ℝ)) + r * finiteEventCount A x at hs
  nlinarith

def shortAlignmentBudgetEvent {Ω : Type*} {T : ℕ} (A : Fin T → Set Ω) (r N : ℕ) : Set Ω :=
  {x | ∃ cost : Fin T → ℕ, (∑ j, cost j) ≤ N ∧ ∀ j, cost j < r → x ∈ A j}

theorem shortAlignmentBudgetEvent_subset {Ω : Type*} {T : ℕ}
    (A : Fin T → Set Ω) (r N : ℕ) (hr : 0 < r) (hN : 2 * N ≤ r * T) :
    shortAlignmentBudgetEvent A r N ⊆ {x | (T : ℝ) / 2 ≤ finiteEventCount A x} := by
  rintro x ⟨cost, hc, hs⟩
  exact short_alignment_count_of_budget A x cost r N hr hc hN hs

theorem pmf_event_mono_toReal {Ω : Type*} [Fintype Ω] (p : PMF Ω)
    (A B : Set Ω) (hAB : A ⊆ B) :
    (p.toOuterMeasure A).toReal ≤ (p.toOuterMeasure B).toReal := by
  classical
  rw [pmf_event_toReal, pmf_event_toReal]
  apply Finset.sum_le_sum
  intro x hx
  by_cases h : x ∈ A
  · simp [h, hAB h]
  · by_cases hB : x ∈ B <;> simp [h, hB, ENNReal.toReal_nonneg]

theorem pmf_two_event_union {Ω : Type*} [Fintype Ω] (p : PMF Ω) (A B : Set Ω) :
    (p.toOuterMeasure (A ∪ B)).toReal ≤ (p.toOuterMeasure A).toReal + (p.toOuterMeasure B).toReal := by
  classical
  simp only [pmf_event_toReal, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;> simp [hA, hB, ENNReal.toReal_nonneg]

theorem pmf_avoid_two_events {Ω : Type*} [Fintype Ω] (p : PMF Ω) (A B : Set Ω)
    (a b : ℝ) (hA : (p.toOuterMeasure A).toReal ≤ a) (hB : (p.toOuterMeasure B).toReal ≤ b) :
    1 - a - b ≤ (p.toOuterMeasure (A ∪ B)ᶜ).toReal := by
  rw [pmf_event_compl_toReal]
  have h := pmf_two_event_union p A B
  linarith

/-- The cross-stage budget implication is now combined with the actual
independent-chain probability bound. Constructing this budget event from a
full-jet algorithm still requires its deterministic simulation and coupling. -/
theorem chain_short_budget_probability {n D k T : ℕ} {κ : Type*} [Fintype κ]
    (hn : 0 < n) (hD : 0 < D) (hT : 0 < T) (hk : k ≤ n)
    (m : ℝ) (hm : 0 ≤ m) (hbalance : 2 * (k : ℝ) = n + m)
    (initialIndex : (j : Fin T) → OtherStageSamples n D k T j → Fin n)
    (ask : (j : Fin T) → OtherStageSamples n D k T j →
      (Fin D → Bool) → List (Fin D → Bool) → Fin n)
    (q N : ℕ) (hbudget : 8 * m + 9 * (q + 1 : ℕ) ≤ n) (hN : 2 * N ≤ (q + 1) * T)
    (w : (j : Fin T) → OtherStageSamples n D k T j → (Fin D → Bool) →
      (Fin q → Fin D → Bool) → κ → EuclideanSpace ℝ (Fin D))
    (hw : ∀ j y b v l, ‖w j y b v l‖ ≤ 1) (a : ℝ) (ha : 0 < a)
    (hqueries : (q + 1 : ℕ) * (m / n) ^ 2 ≤ a ^ 2 / 1024)
    (hdim : 32 * Real.log 2 ≤ a ^ 2 * D)
    (hfamily : (Fintype.card κ : ℝ) ≤ Real.exp (a ^ 2 * D / 4)) :
    ((fixedChainLaw n D k T hk).toOuterMeasure (shortAlignmentBudgetEvent
      (fun j => stageInitializedAlignment j (initialIndex j) (ask j) q (w j) a) (q + 1) N)).toReal ≤ 1 / 2 := by
  refine (pmf_event_mono_toReal _ _ _
    (shortAlignmentBudgetEvent_subset _ (q + 1) N (by omega) hN)).trans ?_
  exact chain_many_short_alignments_le_half hn hD hT hk m hm hbalance initialIndex ask q hbudget
    w hw a ha hqueries hdim hfamily

end FullJet
