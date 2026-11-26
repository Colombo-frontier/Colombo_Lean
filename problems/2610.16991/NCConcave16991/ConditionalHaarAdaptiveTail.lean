import NCConcave16991.ConditionalHaarReveal

/-!
# Actual Haar tails for causal adaptive column-reveal algorithms

All revelation events and probe branches are constructed from an actual
measurable causal state machine. The probability bound is proved by the
masked-run identity and a disjoint finite partition of its true final support.
No conditional-law or stopping-state measurability premise remains.
-/

open Set MeasureTheory
open scoped InnerProductSpace BigOperators

namespace NCConcave16991.Haar.ColumnReveal

noncomputable section

variable {k : ℕ} {S : Type*}

theorem support_card_le (read : S → Fin k) (update : S → EuclideanSpace ℝ (Fin k) → S)
    (initial : S) (oracle : Fin k → EuclideanSpace ℝ (Fin k)) (budget : ℕ) :
    (support read update initial oracle budget).card ≤ budget := by
  exact (Finset.card_image_le).trans_eq (by simp)

abbrev UnseenSupport (k budget : ℕ) (j : Fin k) :=
  {A : Finset (Fin k) // A.card ≤ budget ∧ j ∉ A}

/-- A bounded vector computed by the actual adaptive reveal algorithm has a
small correlation with any column it has not queried. -/
theorem adaptive_probe_tail [MeasurableSpace S]
    (read : S → Fin k) (hread : Measurable read)
    (update : S → EuclideanSpace ℝ (Fin k) → S) (hupdate : Measurable (Function.uncurry update))
    (initial : S) (budget : ℕ) (hbudget : budget < k)
    (g : S → EuclideanSpace ℝ (Fin k)) (hg : Measurable g)
    {C : ℝ} (hC : 0 ≤ C) (hgb : ∀ s, ‖g s‖ ≤ C) (j : Fin k) {r : ℝ} (hr : 0 < r) :
    (haarLaw k).real {Q | j ∉ support read update initial (columnOracle Q) budget ∧
      r ≤ |⟪g (run read update initial (columnOracle Q) budget), columnOracle Q j⟫_ℝ|} ≤
      C ^ 2 / (((k - budget : ℕ) : ℝ) * r ^ 2) := by
  let E : UnseenSupport k budget j → Set (OrthogonalGroup k) := fun A ↦
    {Q | support read update initial (columnOracle Q) budget = A.val}
  let a : UnseenSupport k budget j → OrthogonalGroup k → EuclideanSpace ℝ (Fin k) := fun A Q ↦
    g (run read update initial (maskedColumn A.val Q) budget)
  have hE (A : UnseenSupport k budget j) : MeasurableSet[columnSigma A.val] (E A) :=
    support_fiber_measurable read hread update hupdate initial A.val budget
  have ha (A : UnseenSupport k budget j) : StronglyMeasurable[columnSigma A.val] (a A) := by
    letI : MeasurableSpace (OrthogonalGroup k) := columnSigma A.val
    exact (hg.comp (masked_run_measurable read hread update hupdate initial A.val budget)).stronglyMeasurable
  have hdisj : Pairwise (fun A B ↦ Disjoint (E A) (E B)) := by
    intro A B hAB
    apply Set.disjoint_left.mpr
    intro Q hQA hQB
    exact hAB (Subtype.ext (hQA.symm.trans hQB))
  have hmass : (∑ A : UnseenSupport k budget j, (haarLaw k).real (E A)) ≤ 1 := by
    have he := measureReal_iUnion_fintype (μ := haarLaw k) hdisj
      (fun A ↦ columnSigma_le A.val _ (hE A))
    have hm := measureReal_mono (μ := haarLaw k) (s₁ := ⋃ A, E A) (s₂ := univ) (subset_univ _)
    rw [he] at hm
    simpa using hm
  have he : {Q : OrthogonalGroup k | j ∉ support read update initial (columnOracle Q) budget ∧
        r ≤ |⟪g (run read update initial (columnOracle Q) budget), columnOracle Q j⟫_ℝ|} =
      ⋃ A : UnseenSupport k budget j, E A ∩ {Q | r ≤ |⟪a A Q, columnOracle Q j⟫_ℝ|} := by
    ext Q
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · rintro ⟨hj, hbad⟩
      let A : UnseenSupport k budget j :=
        ⟨support read update initial (columnOracle Q) budget,
          support_card_le read update initial (columnOracle Q) budget, hj⟩
      refine ⟨A, rfl, ?_⟩
      have heq := run_eq_masked_on_support_fiber read update initial A.val Q budget rfl
      change r ≤ |⟪g (run read update initial (maskedColumn A.val Q) budget), columnOracle Q j⟫_ℝ|
      rwa [← heq]
    · rintro ⟨A, hA, hbad⟩
      change support read update initial (columnOracle Q) budget = A.val at hA
      refine ⟨hA ▸ A.property.2, ?_⟩
      rw [run_eq_masked_on_support_fiber read update initial A.val Q budget hA]
      exact hbad
  have hd : (0 : ℝ) < (k - budget : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hbudget
  have hden (A : UnseenSupport k budget j) : k - budget ≤ A.valᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  have hbound (A : UnseenSupport k budget j) :
      C ^ 2 / ((A.valᶜ.card : ℝ) * r ^ 2) ≤ C ^ 2 / (((k - budget : ℕ) : ℝ) * r ^ 2) := by
    apply div_le_div_of_nonneg_left (sq_nonneg C) (mul_pos hd (sq_pos_of_pos hr))
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hden A) (sq_nonneg r)
  have hb : 0 ≤ C ^ 2 / (((k - budget : ℕ) : ℝ) * r ^ 2) := by positivity
  rw [he]
  calc
    _ ≤ ∑ A : UnseenSupport k budget j, (haarLaw k).real
        (E A ∩ {Q | r ≤ |⟪a A Q, columnOracle Q j⟫_ℝ|}) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ A : UnseenSupport k budget j, (haarLaw k).real (E A) *
        (C ^ 2 / ((A.valᶜ.card : ℝ) * r ^ 2)) := by
      apply Finset.sum_le_sum
      intro A hA
      exact observed_inner_tail_on_event A.val (a A) (ha A) hC (fun Q ↦ hgb _)
        j A.property.2 hr (hE A)
    _ ≤ ∑ A : UnseenSupport k budget j, (haarLaw k).real (E A) *
        (C ^ 2 / (((k - budget : ℕ) : ℝ) * r ^ 2)) :=
      Finset.sum_le_sum (fun A _ ↦ mul_le_mul_of_nonneg_left (hbound A) measureReal_nonneg)
    _ = (∑ A : UnseenSupport k budget j, (haarLaw k).real (E A)) *
        (C ^ 2 / (((k - budget : ℕ) : ℝ) * r ^ 2)) := by rw [Finset.sum_mul]
    _ ≤ 1 * (C ^ 2 / (((k - budget : ℕ) : ℝ) * r ^ 2)) := mul_le_mul_of_nonneg_right hmass hb
    _ = _ := one_mul _

end

end NCConcave16991.Haar.ColumnReveal
