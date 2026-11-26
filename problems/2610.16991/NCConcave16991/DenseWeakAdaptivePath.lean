import NCConcave16991.DenseWeakAdaptiveSequence

/-! # The exact queried row set along an adaptive response history -/

namespace NCConcave16991.DenseWeakHiding.RowExperiment

variable {I D Y : Type*} {r : ℕ}

theorem pathRow_extend_snoc (E : RowExperiment I D Y r)
    (nextRow : (Fin r → D → Y) → I) (h : Fin r → D → Y) (y : D → Y) :
    (E.extend nextRow).pathRow (Fin.snoc h y) = Fin.snoc (E.pathRow h) (nextRow h) := by
  induction E with
  | done =>
      have he : h = Fin.elim0 := funext (fun i ↦ Fin.elim0 i)
      subst h
      ext t
      have ht : t = 0 := Fin.ext (by omega)
      subst t
      rfl
  | @query r i next ih =>
      rw [← Fin.cons_self_tail h]
      simp only [← Fin.cons_snoc_eq_snoc_cons, extend, pathRow, Fin.cons_zero,
        Fin.tail_cons, ih]

theorem observedRows_extend_snoc [DecidableEq I] (E : RowExperiment I D Y r)
    (nextRow : (Fin r → D → Y) → I) (h : Fin r → D → Y) (y : D → Y) :
    (E.extend nextRow).observedRows (Fin.snoc h y) = insert (nextRow h) (E.observedRows h) := by
  unfold observedRows
  rw [pathRow_extend_snoc]
  ext i
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  have he := congrArg (fun A : Set I ↦ i ∈ A) (Fin.range_snoc (E.pathRow h) (nextRow h))
  simpa only [Set.mem_range, Set.mem_insert_iff] using Iff.of_eq he

theorem observedRows_policy_succ [DecidableEq I]
    (nextRow : ∀ t : ℕ, (Fin t → D → Y) → I) (t : ℕ)
    (h : Fin (t + 1) → D → Y) :
    (policyExperiment nextRow (t + 1)).observedRows h =
      insert (nextRow t (Fin.init h)) ((policyExperiment nextRow t).observedRows (Fin.init h)) := by
  rw [← Fin.snoc_init_self h]
  simpa only [policyExperiment, Fin.init_snoc] using
    observedRows_extend_snoc (policyExperiment nextRow t) (nextRow t) (Fin.init h) (h (Fin.last t))

end NCConcave16991.DenseWeakHiding.RowExperiment
