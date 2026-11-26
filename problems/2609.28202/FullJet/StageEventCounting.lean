import FullJet.IndependentStages

open scoped BigOperators

namespace FullJet

noncomputable def finiteEventCount {Ω ι : Type*} [Fintype ι] (A : ι → Set Ω) (ω : Ω) : ℝ :=
  ∑ j, (A j).indicator (fun _ => (1 : ℝ)) ω

theorem finiteEventCount_nonneg {Ω ι : Type*} [Fintype ι] (A : ι → Set Ω) (ω : Ω) :
    0 ≤ finiteEventCount A ω := by
  classical
  apply Finset.sum_nonneg
  intro j hj
  simp only [Set.indicator_apply]
  split_ifs <;> norm_num

theorem pmf_event_count_expectation {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (p : PMF Ω) (A : ι → Set Ω) :
    ∑ ω, (p ω).toReal * finiteEventCount A ω = ∑ j, (p.toOuterMeasure (A j)).toReal := by
  classical
  unfold finiteEventCount
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pmf_event_toReal]
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases h : ω ∈ A j <;> simp [Set.indicator_apply, h]

theorem pmf_finite_markov {Ω : Type*} [Fintype Ω] (p : PMF Ω)
    (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω) (c : ℝ) (hc : 0 < c) :
    (p.toOuterMeasure {ω | c ≤ X ω}).toReal ≤ (∑ ω, (p ω).toReal * X ω) / c := by
  classical
  apply (le_div_iff₀ hc).mpr
  rw [pmf_event_toReal, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω hω
  by_cases h : c ≤ X ω
  · simp only [Set.mem_setOf_eq, h, if_true]
    exact mul_le_mul_of_nonneg_left h ENNReal.toReal_nonneg
  · simp only [Set.mem_setOf_eq, h, if_false, zero_mul]
    exact mul_nonneg ENNReal.toReal_nonneg (hX ω)

theorem pmf_many_events_le {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (p : PMF Ω) (A : ι → Set Ω) (δ c : ℝ) (hc : 0 < c)
    (hA : ∀ j, (p.toOuterMeasure (A j)).toReal ≤ δ) :
    (p.toOuterMeasure {ω | c ≤ finiteEventCount A ω}).toReal ≤ Fintype.card ι * δ / c := by
  have h := pmf_finite_markov p (finiteEventCount A) (finiteEventCount_nonneg A) c hc
  rw [pmf_event_count_expectation] at h
  refine h.trans (div_le_div_of_nonneg_right ?_ hc.le)
  calc
    _ ≤ ∑ _ : ι, δ := Finset.sum_le_sum (fun j _ => hA j)
    _ = _ := by simp

theorem pmf_union_bound {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (p : PMF Ω) (A : ι → Set Ω) :
    (p.toOuterMeasure {ω | ∃ j, ω ∈ A j}).toReal ≤ ∑ j, (p.toOuterMeasure (A j)).toReal := by
  classical
  simpa only [pmf_event_toReal, Finset.sum_filter, Set.mem_setOf_eq] using
    finite_union_bound (fun ω => (p ω).toReal) (fun _ => ENNReal.toReal_nonneg) (fun j ω => ω ∈ A j)

/-- For an actual independent chain, at most half the probability mass can
align at least half the stages using these short initialized runs. The stage
events themselves need not be independent. -/
theorem chain_many_short_alignments_le_half {n D k T : ℕ} {κ : Type*} [Fintype κ]
    (hn : 0 < n) (hD : 0 < D) (hT : 0 < T) (hk : k ≤ n)
    (m : ℝ) (hm : 0 ≤ m) (hbalance : 2 * (k : ℝ) = n + m)
    (initialIndex : (j : Fin T) → OtherStageSamples n D k T j → Fin n)
    (ask : (j : Fin T) → OtherStageSamples n D k T j →
      (Fin D → Bool) → List (Fin D → Bool) → Fin n)
    (q : ℕ) (hbudget : 8 * m + 9 * (q + 1 : ℕ) ≤ n)
    (w : (j : Fin T) → OtherStageSamples n D k T j → (Fin D → Bool) →
      (Fin q → Fin D → Bool) → κ → EuclideanSpace ℝ (Fin D))
    (hw : ∀ j y b v l, ‖w j y b v l‖ ≤ 1) (a : ℝ) (ha : 0 < a)
    (hqueries : (q + 1 : ℕ) * (m / n) ^ 2 ≤ a ^ 2 / 1024)
    (hdim : 32 * Real.log 2 ≤ a ^ 2 * D)
    (hfamily : (Fintype.card κ : ℝ) ≤ Real.exp (a ^ 2 * D / 4)) :
    ((fixedChainLaw n D k T hk).toOuterMeasure {x | (T : ℝ) / 2 ≤
      finiteEventCount (fun j => stageInitializedAlignment j (initialIndex j) (ask j) q (w j) a) x}).toReal ≤
      1 / 2 := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have h := pmf_many_events_le (fixedChainLaw n D k T hk)
    (fun j => stageInitializedAlignment j (initialIndex j) (ask j) q (w j) a)
    (1 / 4) ((T : ℝ) / 2) (by positivity)
    (fun j => stage_initialized_alignment_quarter hn hD hk m hm hbalance j
      (initialIndex j) (ask j) q hbudget (w j) (hw j) a ha hqueries hdim hfamily)
  simp only [Fintype.card_fin] at h
  have hconst : (T : ℝ) * (1 / 4) / ((T : ℝ) / 2) = 1 / 2 := by
    field_simp
    ring
  rwa [hconst] at h

end FullJet
