import FullJet.VectorRows
import FullJet.TranscriptLaw

namespace FullJet

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]

def vectorQueriedLabels (ask : List (ι → Bool) → α) (past : List (ι → Bool)) :
    List (ι → Bool) → Finset α
  | [] => ∅
  | b :: bs => insert (ask past) (vectorQueriedLabels ask (past ++ [b]) bs)

theorem vectorLabels_union (ask : List (ι → Bool) → α)
    (past rows : List (ι → Bool)) (j : ι) :
    vectorPositiveLabels ask past rows j ∪ vectorNegativeLabels ask past rows j =
      vectorQueriedLabels ask past rows := by
  induction rows generalizing past with
  | nil => rfl
  | cons b bs ih =>
    cases hb : b j <;> simp [vectorPositiveLabels, vectorNegativeLabels,
      vectorQueriedLabels, hb, Finset.insert_union, Finset.union_insert, ih]

theorem vectorQueriedLabels_card_le (ask : List (ι → Bool) → α)
    (past rows : List (ι → Bool)) : (vectorQueriedLabels ask past rows).card ≤ rows.length := by
  induction rows generalizing past with
  | nil => simp [vectorQueriedLabels]
  | cons b bs ih =>
    exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (ih _) 1)

theorem vectorPositiveLabels_card_le (ask : List (ι → Bool) → α)
    (past rows : List (ι → Bool)) (j : ι) :
    (vectorPositiveLabels ask past rows j).card ≤ rows.length := by
  have h := Finset.card_le_card (show vectorPositiveLabels ask past rows j ⊆
    vectorPositiveLabels ask past rows j ∪ vectorNegativeLabels ask past rows j from
      Finset.subset_union_left)
  rw [vectorLabels_union] at h
  exact h.trans (vectorQueriedLabels_card_le ask past rows)

theorem vectorNegativeLabels_card_le (ask : List (ι → Bool) → α)
    (past rows : List (ι → Bool)) (j : ι) :
    (vectorNegativeLabels ask past rows j).card ≤ rows.length := by
  have h := Finset.card_le_card (show vectorNegativeLabels ask past rows j ⊆
    vectorPositiveLabels ask past rows j ∪ vectorNegativeLabels ask past rows j from
      Finset.subset_union_right)
  rw [vectorLabels_union] at h
  exact h.trans (vectorQueriedLabels_card_le ask past rows)

theorem vectorRowAnswers_validHistory (ask : List (ι → Bool) → α)
    (S : ι → Finset α) (past rows : List (ι → Bool)) :
    vectorRowAnswers ask S past rows.length = rows ↔
      validHistory (fun S hist j => decide (ask hist ∈ S j)) S past rows := by
  induction rows generalizing past with
  | nil => simp [vectorRowAnswers, validHistory]
  | cons b bs ih =>
    simp only [List.length_cons, vectorRowAnswers, List.cons.injEq, validHistory]
    constructor
    · rintro ⟨hb, ht⟩
      exact ⟨hb, (ih (past ++ [b])).mp (by simpa only [hb] using ht)⟩
    · rintro ⟨hb, ht⟩
      exact ⟨hb, by simpa only [hb] using (ih (past ++ [b])).mpr ht⟩

theorem vectorColumnLaw_history_feasible_iff (U : Finset α) (k : ι → ℕ)
    (hk : ∀ j, k j ≤ U.card) (ask : List (ι → Bool) → α) (past rows : List (ι → Bool)) :
    (∃ S ∈ {S | vectorRowAnswers ask S past rows.length = rows},
      S ∈ (vectorColumnLaw U k hk).support) ↔
      ∀ j, (compatibleColumnSamples U k ask past rows j).Nonempty := by
  constructor
  · exact vectorColumnLaw_history_feasible U k hk ask past rows
  · intro h
    obtain ⟨S, hS⟩ := Fintype.piFinset_nonempty.mpr h
    have hmem := Fintype.mem_piFinset.mp hS
    refine ⟨S, (vectorRowAnswers_eq_iff ask S past rows).mpr (fun j =>
      (Finset.mem_filter.mp (hmem j)).2), ?_⟩
    simpa only [vectorColumnLaw, uniformPi, PMF.mem_support_uniformOfFinset_iff] using
      Fintype.mem_piFinset.mpr (fun j => (Finset.mem_filter.mp (hmem j)).1)

theorem compatibleColumnSamples_nonempty_of_counts [Fintype α]
    (k : ι → ℕ) (hk : ∀ j, k j ≤ Fintype.card α)
    (ask : List (ι → Bool) → α) (past rows : List (ι → Bool)) (j : ι)
    (hPN : Disjoint (vectorPositiveLabels ask past rows j) (vectorNegativeLabels ask past rows j))
    (hP : (vectorPositiveLabels ask past rows j).card ≤ k j)
    (hN : (vectorNegativeLabels ask past rows j).card ≤ Fintype.card α - k j) :
    (compatibleColumnSamples Finset.univ k ask past rows j).Nonempty := by
  let P := vectorPositiveLabels ask past rows j
  let N := vectorNegativeLabels ask past rows j
  have hcard : (P ∪ N).card = P.card + N.card := Finset.card_union_of_disjoint hPN
  have hrem : k j - P.card ≤ (Finset.univ \ (P ∪ N)).card := by
    rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ, hcard]
    have hk' := hk j
    change P.card ≤ k j at hP
    change N.card ≤ Fintype.card α - k j at hN
    omega
  change ((Finset.univ.powersetCard (k j)).filter (compatibleColumn P N)).Nonempty
  rw [powersetCard_filter_compatible _ _ _ _ (Finset.subset_univ _) hPN hP]
  exact (Finset.powersetCard_nonempty.mpr hrem).image _

/-- A short realizable history for one fixed-column bias is realizable for
every other bias having enough positive and negative entries. -/
theorem vectorColumnLaw_history_transfer [Fintype α]
    (k k' : ι → ℕ) (hk : ∀ j, k j ≤ Fintype.card α) (hk' : ∀ j, k' j ≤ Fintype.card α)
    (ask : List (ι → Bool) → α) (past rows : List (ι → Bool))
    (hshortP : ∀ j, rows.length ≤ k' j) (hshortN : ∀ j, rows.length ≤ Fintype.card α - k' j)
    (hpos : ∃ S ∈ {S | vectorRowAnswers ask S past rows.length = rows},
      S ∈ (vectorColumnLaw Finset.univ k (by simpa using hk)).support) :
    ∃ S ∈ {S | vectorRowAnswers ask S past rows.length = rows},
      S ∈ (vectorColumnLaw Finset.univ k' (by simpa using hk')).support := by
  apply (vectorColumnLaw_history_feasible_iff _ _ _ _ _ _).mpr
  intro j
  obtain ⟨S, hS⟩ := vectorColumnLaw_history_feasible _ _ _ _ _ _ hpos j
  obtain ⟨hmem, hc⟩ := Finset.mem_filter.mp hS
  have hPN := (compatibleColumn_feasible _ _ _ _ _ hmem hc).2.1
  exact compatibleColumnSamples_nonempty_of_counts k' hk' ask past rows j hPN
    ((vectorPositiveLabels_card_le ask past rows j).trans (hshortP j))
    ((vectorNegativeLabels_card_le ask past rows j).trans (hshortN j))

theorem compatible_history_repeated_answer (ask : List (ι → Bool) → α)
    (S : ι → Finset α) (past rows : List (ι → Bool))
    (hrows : vectorRowAnswers ask S past rows.length = rows)
    (i : α) (hi : i ∈ vectorQueriedLabels ask past rows) :
    (fun j => decide (i ∈ S j)) =
      fun j => decide (i ∈ vectorPositiveLabels ask past rows j) := by
  funext j
  have hc := (vectorRowAnswers_eq_iff ask S past rows).mp hrows j
  have hi' : i ∈ vectorPositiveLabels ask past rows j ∪ vectorNegativeLabels ask past rows j :=
    (vectorLabels_union ask past rows j).symm ▸ hi
  rcases Finset.mem_union.mp hi' with hP | hN
  · simp [hP, hc.1 hP]
  · have hS : i ∉ S j := fun h => Finset.disjoint_left.mp hc.2 hN h
    have hP : i ∉ vectorPositiveLabels ask past rows j := fun h => hS (hc.1 h)
    simp [hS, hP]

end FullJet
