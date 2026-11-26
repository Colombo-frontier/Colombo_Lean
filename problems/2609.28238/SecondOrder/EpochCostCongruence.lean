import SecondOrder.EpochTreeCost

open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

theorem epochBoundary_congr {N q : ℕ} {g h : ℕ → Bool}
    (he : ∀ t < N, epochOfStep q g t=epochOfStep q h t) (e : ℕ) :
    epochBoundary N q g e=epochBoundary N q h e := by
  apply Nat.le_antisymm
  · apply (epochBoundary_le_iff N q g e _).mpr
    by_cases ht : N ≤ epochBoundary N q h e
    · exact Or.inl ht
    · right
      rw [he _ (Nat.lt_of_not_ge ht)]
      exact ((epochBoundary_le_iff N q h e _).mp le_rfl).resolve_left ht
  · apply (epochBoundary_le_iff N q h e _).mpr
    by_cases ht : N ≤ epochBoundary N q g e
    · exact Or.inl ht
    · right
      rw [← he _ (Nat.lt_of_not_ge ht)]
      exact ((epochBoundary_le_iff N q g e _).mp le_rfl).resolve_left ht

theorem idealEpochBegin_congr {d M : ℕ} (q : ℕ) (Lip s : ℝ) (a b : IdealPolicy d) (w : Fin M → Bool)
    (hp : ∀ t ≤ M, idealPath Lip s a (extendSigns w) t=idealPath Lip s b (extendSigns w) t) (e : ℕ) :
    idealEpochBegin q Lip s a w e=idealEpochBegin q Lip s b w e := by
  have hn : idealPhysicalLength Lip s a w=idealPhysicalLength Lip s b w := by
    simpa only [idealPath_extendSigns] using congrArg stateMoves (hp M le_rfl)
  unfold idealEpochBegin
  rw [← hn]
  apply epochBoundary_congr
  intro t ht
  unfold epochOfStep
  rw [idealGradientFlag_count,idealGradientFlag_count,hp t (ht.le.trans (idealPhysicalLength_le Lip s a w))]

theorem idealEpochLength_congr {d M : ℕ} (q : ℕ) (Lip s : ℝ) (a b : IdealPolicy d) (w : Fin M → Bool)
    (hp : ∀ t ≤ M, idealPath Lip s a (extendSigns w) t=idealPath Lip s b (extendSigns w) t) (e : ℕ) :
    idealEpochLength q Lip s a w e=idealEpochLength q Lip s b w e := by
  change idealEpochBegin q Lip s a w (e+1)-idealEpochBegin q Lip s a w e =
    idealEpochBegin q Lip s b w (e+1)-idealEpochBegin q Lip s b w e
  rw [idealEpochBegin_congr q Lip s a b w hp,idealEpochBegin_congr q Lip s a b w hp]

theorem idealEpochPath_congr {d M : ℕ} (q : ℕ) (Lip s : ℝ) (a b : IdealPolicy d) (w : Fin M → Bool)
    (hp : ∀ t ≤ M, idealPath Lip s a (extendSigns w) t=idealPath Lip s b (extendSigns w) t) (e k : ℕ) :
    idealEpochPath q Lip s a w e k=idealEpochPath q Lip s b w e k := by
  simp only [idealEpochPath]
  rw [← idealEpochBegin_congr q Lip s a b w hp,← idealEpochLength_congr q Lip s a b w hp]
  apply congrArg IdealState.point
  apply hp
  have hb := epochLength_add_start (idealPhysicalLength Lip s a w) q
    (idealGradientFlag Lip s a (extendSigns w)) e
  have hc := (epochBoundary_le_cap (idealPhysicalLength Lip s a w) q
    (idealGradientFlag Lip s a (extendSigns w)) (e+1)).trans (idealPhysicalLength_le Lip s a w)
  change idealEpochBegin q Lip s a w e+idealEpochLength q Lip s a w e=idealEpochBegin q Lip s a w (e+1) at hb
  change idealEpochBegin q Lip s a w (e+1) ≤ M at hc
  omega

/-- All epoch tree costs depend only on the actual finite physical state
history. Extending a policy differently after the cap does not change them. -/
theorem idealEpochTreeQueries_congr {d M : ℕ} (P : Parameters) (q : ℕ) (Lip s : ℝ)
    (a b : IdealPolicy d) (w : Fin M → Bool)
    (hp : ∀ t ≤ M, idealPath Lip s a (extendSigns w) t=idealPath Lip s b (extendSigns w) t)
    (L : ℕ) (ρ δ : ℝ) :
    idealEpochTreeQueries P q Lip s a w L ρ δ=idealEpochTreeQueries P q Lip s b w L ρ δ := by
  unfold idealEpochTreeQueries
  apply Finset.sum_congr rfl
  intro e he
  rw [idealEpochLength_congr q Lip s a b w hp]
  unfold treeQueryCount
  apply Finset.sum_congr rfl
  intro i hi
  rw [idealEpochPath_congr q Lip s a b w hp,idealEpochPath_congr q Lip s a b w hp]

end
end SecondOrder
