import NCConcave16991.DenseWeakAdaptiveSequence

/-! # Every earlier adaptive response transcript is contained in the final one -/

namespace NCConcave16991.DenseWeakHiding.RowExperiment

variable {I D Y A : Type*}

theorem run_policyExperiment_prefix (read : A → I → Y)
    (nextRow : ∀ t : ℕ, (Fin t → D → Y) → I) (bank : D → A)
    (r : ℕ) (t : ℕ) (ht : t ≤ r) (i : Fin t) :
    (policyExperiment nextRow t).run read bank i =
      (policyExperiment nextRow r).run read bank (Fin.castLE ht i) := by
  induction r generalizing t with
  | zero =>
      have hi := i.isLt
      omega
  | succ r ih =>
      by_cases htr : t ≤ r
      · rw [run_policyExperiment_succ]
        have hi := ih t htr i
        rw [hi]
        have he : Fin.castLE ht i = (Fin.castLE htr i).castSucc := Fin.ext rfl
        rw [he, Fin.snoc_castSucc]
      · have he : t = r + 1 := by omega
        subst t
        rfl

end NCConcave16991.DenseWeakHiding.RowExperiment
