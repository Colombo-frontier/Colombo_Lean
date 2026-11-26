import NCConcave16991.ConditionalHaarOptionalAdaptiveTail

/-! # Finite actual query and output tails for an adaptive reveal run -/

open Set MeasureTheory
open scoped InnerProductSpace BigOperators

namespace NCConcave16991.Haar.OptionalReveal

noncomputable section

variable {k : ℕ} {S : Type*} [MeasurableSpace S]

theorem run_measurable (read : S → Option (Fin k)) (hread : Measurable read)
    (update : S → EuclideanSpace ℝ (Fin k) → S) (hupdate : Measurable (Function.uncurry update))
    (initial : S) (t : ℕ) : Measurable (fun Q ↦ run read update initial (ColumnReveal.columnOracle Q) t) := by
  have hm := masked_run_measurable read hread update hupdate initial Finset.univ t
  have hmono := hm.mono (columnSigma_le Finset.univ) le_rfl
  have he (Q : OrthogonalGroup k) : ColumnReveal.maskedColumn Finset.univ Q = ColumnReveal.columnOracle Q := by
    funext i
    exact ColumnReveal.maskedColumn_eq_of_mem _ _ _ (Finset.mem_univ _)
  simpa only [he] using hmono

theorem unqueried_event_measurable (read : S → Option (Fin k)) (hread : Measurable read)
    (update : S → EuclideanSpace ℝ (Fin k) → S) (hupdate : Measurable (Function.uncurry update))
    (initial : S) (budget : ℕ) (j : Fin k) :
    MeasurableSet {Q | j ∉ support read update initial (ColumnReveal.columnOracle Q) budget} := by
  have hmeas (t : Fin budget) : MeasurableSet
      {Q | read (run read update initial (ColumnReveal.columnOracle Q) t.val) ≠ some j} := by
    have he : MeasurableSet {Q | read (run read update initial (ColumnReveal.columnOracle Q) t.val) = some j} :=
      (hread.comp (run_measurable read hread update hupdate initial t.val)) (measurableSet_singleton (some j))
    exact he.compl
  have hall : MeasurableSet {Q : OrthogonalGroup k | ∀ t : Fin budget,
      read (run read update initial (ColumnReveal.columnOracle Q) t.val) ≠ some j} := by
    simpa only [Set.ofPred_forall] using MeasurableSet.iInter hmeas
  simpa [support, eq_comm] using hall

theorem adaptive_probe_bad_measurable (read : S → Option (Fin k)) (hread : Measurable read)
    (update : S → EuclideanSpace ℝ (Fin k) → S) (hupdate : Measurable (Function.uncurry update))
    (initial : S) (budget : ℕ) (g : S → EuclideanSpace ℝ (Fin k)) (hg : Measurable g)
    (j : Fin k) (r : ℝ) :
    MeasurableSet {Q | j ∉ support read update initial (ColumnReveal.columnOracle Q) budget ∧
      r ≤ |⟪g (run read update initial (ColumnReveal.columnOracle Q) budget), ColumnReveal.columnOracle Q j⟫_ℝ|} := by
  have hm : Measurable (fun Q ↦ ⟪g (run read update initial (ColumnReveal.columnOracle Q) budget), ColumnReveal.columnOracle Q j⟫_ℝ) :=
    (hg.comp (run_measurable read hread update hupdate initial budget)).inner
    (continuous_orthogonalLinearIsometryEquiv_apply (basisVector j)).measurable
  exact (unqueried_event_measurable read hread update hupdate initial budget j).inter
    (measurableSet_le measurable_const (continuous_abs.measurable.comp hm))

/-- Each probe is computed from the actual state at its specified query time.
The final output can be included as one more measurable bounded probe. -/
theorem finite_adaptive_probe_union_tail {N : ℕ}
    (read : S → Option (Fin k)) (hread : Measurable read)
    (update : S → EuclideanSpace ℝ (Fin k) → S) (hupdate : Measurable (Function.uncurry update))
    (initial : S) (budget : ℕ) (hbudget : budget < k)
    (time : Fin N → ℕ) (htime : ∀ t, time t ≤ budget)
    (g : Fin N → S → EuclideanSpace ℝ (Fin k)) (hg : ∀ t, Measurable (g t))
    {C : ℝ} (hC : 0 ≤ C) (hgb : ∀ t s, ‖g t s‖ ≤ C)
    (j : Fin N → Fin k) {r : ℝ} (hr : 0 < r) :
    (haarLaw k).real {Q | ∃ t, j t ∉ support read update initial (ColumnReveal.columnOracle Q) (time t) ∧
      r ≤ |⟪g t (run read update initial (ColumnReveal.columnOracle Q) (time t)), ColumnReveal.columnOracle Q (j t)⟫_ℝ|} ≤
      (N : ℝ) * C ^ 2 / (((k - budget : ℕ) : ℝ) * r ^ 2) := by
  have hd : (0 : ℝ) < (k - budget : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hbudget
  have he : {Q : OrthogonalGroup k | ∃ t, j t ∉ support read update initial (ColumnReveal.columnOracle Q) (time t) ∧
        r ≤ |⟪g t (run read update initial (ColumnReveal.columnOracle Q) (time t)), ColumnReveal.columnOracle Q (j t)⟫_ℝ|} =
      ⋃ t : Fin N, {Q | j t ∉ support read update initial (ColumnReveal.columnOracle Q) (time t) ∧
        r ≤ |⟪g t (run read update initial (ColumnReveal.columnOracle Q) (time t)), ColumnReveal.columnOracle Q (j t)⟫_ℝ|} := by
    ext Q
    simp
  have htail (t : Fin N) :
      (haarLaw k).real {Q | j t ∉ support read update initial (ColumnReveal.columnOracle Q) (time t) ∧
        r ≤ |⟪g t (run read update initial (ColumnReveal.columnOracle Q) (time t)), ColumnReveal.columnOracle Q (j t)⟫_ℝ|} ≤
      C ^ 2 / (((k - budget : ℕ) : ℝ) * r ^ 2) := by
    apply (adaptive_probe_tail read hread update hupdate initial (time t)
      ((htime t).trans_lt hbudget) (g t) (hg t) hC (hgb t) (j t) hr).trans
    apply div_le_div_of_nonneg_left (sq_nonneg C) (mul_pos hd (sq_pos_of_pos hr))
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le_sub_left (htime t) k) (sq_nonneg r)
  rw [he]
  calc
    _ ≤ ∑ t : Fin N, (haarLaw k).real {Q | j t ∉ support read update initial (ColumnReveal.columnOracle Q) (time t) ∧
        r ≤ |⟪g t (run read update initial (ColumnReveal.columnOracle Q) (time t)), ColumnReveal.columnOracle Q (j t)⟫_ℝ|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _t : Fin N, C ^ 2 / (((k - budget : ℕ) : ℝ) * r ^ 2) := Finset.sum_le_sum (fun t _ ↦ htail t)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end

end NCConcave16991.Haar.OptionalReveal

