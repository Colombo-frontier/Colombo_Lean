import FullJet.RowReplyLaw
import FullJet.VectorHistoryFacts
import FullJet.BoundedTranscript

open scoped BigOperators

namespace FullJet

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

theorem vectorColumnLaw_repeated_row (U : Finset α) (k : ι → ℕ)
    (hk : ∀ j, k j ≤ U.card) (ask : List (ι → Bool) → α) (past rows : List (ι → Bool))
    (hpos : ∃ S ∈ {S | vectorRowAnswers ask S past rows.length = rows},
      S ∈ (vectorColumnLaw U k hk).support) (i : α)
    (hi : i ∈ vectorQueriedLabels ask past rows) :
    ((vectorColumnLaw U k hk).filter {S | vectorRowAnswers ask S past rows.length = rows} hpos).map
      (fun S j => decide (i ∈ S j)) =
      PMF.pure (fun j => decide (i ∈ vectorPositiveLabels ask past rows j)) := by
  apply pmf_map_eq_pure_of_support
  intro S hS
  exact compatible_history_repeated_answer ask S past rows
    ((PMF.mem_support_filter_iff hpos).mp hS).1 i hi

theorem historyKernel_vector_active (U : Finset α) (k : ι → ℕ)
    (hk : ∀ j, k j ≤ U.card) (ask : List (ι → Bool) → α)
    (past rows : List (ι → Bool)) (fallback : ι → Bool)
    (hpos : ∃ S ∈ {S | vectorRowAnswers ask S past rows.length = rows},
      S ∈ (vectorColumnLaw U k hk).support) :
    historyKernel (vectorColumnLaw U k hk) (fun S hist j => decide (ask hist ∈ S j))
      past fallback rows =
      ((vectorColumnLaw U k hk).filter {S | vectorRowAnswers ask S past rows.length = rows} hpos).map
        (fun S j => decide (ask (past ++ rows) ∈ S j)) := by
  classical
  have hevent : historyEvent (fun (S : ι → Finset α) hist j => decide (ask hist ∈ S j)) past rows =
      {S | vectorRowAnswers ask S past rows.length = rows} := by
    ext S
    exact (vectorRowAnswers_validHistory ask S past rows).symm
  unfold historyKernel
  simp only [hevent, dif_pos hpos]

theorem historyKernel_vector_inactive (U : Finset α) (k : ι → ℕ)
    (hk : ∀ j, k j ≤ U.card) (ask : List (ι → Bool) → α)
    (past rows : List (ι → Bool)) (fallback : ι → Bool)
    (hpos : ¬ ∃ S ∈ {S | vectorRowAnswers ask S past rows.length = rows},
      S ∈ (vectorColumnLaw U k hk).support) :
    historyKernel (vectorColumnLaw U k hk) (fun S hist j => decide (ask hist ∈ S j))
      past fallback rows = PMF.pure fallback := by
  classical
  have hevent : historyEvent (fun (S : ι → Finset α) hist j => decide (ask hist ∈ S j)) past rows =
      {S | vectorRowAnswers ask S past rows.length = rows} := by
    ext S
    exact (vectorRowAnswers_validHistory ask S past rows).symm
  unfold historyKernel
  simp only [hevent, dif_neg hpos]

def vectorHistorySize (ask : List (ι → Bool) → α) (past rows : List (ι → Bool)) : ℕ :=
  (vectorQueriedLabels ask past rows).card

def vectorHistorySum (ask : List (ι → Bool) → α) (past rows : List (ι → Bool)) (j : ι) : ℝ :=
  (vectorPositiveLabels ask past rows j).card - (vectorNegativeLabels ask past rows j).card

theorem vectorHistorySum_bounds (ask : List (ι → Bool) → α) (past rows : List (ι → Bool)) (j : ι) :
    -(vectorHistorySize ask past rows : ℝ) ≤ vectorHistorySum ask past rows j ∧
      vectorHistorySum ask past rows j ≤ vectorHistorySize ask past rows := by
  have hP := Finset.card_le_card (show vectorPositiveLabels ask past rows j ⊆
    vectorPositiveLabels ask past rows j ∪ vectorNegativeLabels ask past rows j from Finset.subset_union_left)
  have hN := Finset.card_le_card (show vectorNegativeLabels ask past rows j ⊆
    vectorPositiveLabels ask past rows j ∪ vectorNegativeLabels ask past rows j from Finset.subset_union_right)
  rw [vectorLabels_union] at hP hN
  have hP' : ((vectorPositiveLabels ask past rows j).card : ℝ) ≤ vectorHistorySize ask past rows :=
    by exact_mod_cast hP
  have hN' : ((vectorNegativeLabels ask past rows j).card : ℝ) ≤ vectorHistorySize ask past rows :=
    by exact_mod_cast hN
  have hP0 : (0 : ℝ) ≤ (vectorPositiveLabels ask past rows j).card := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ (vectorNegativeLabels ask past rows j).card := Nat.cast_nonneg _
  unfold vectorHistorySum
  constructor <;> linarith

/-- Convert the actual residual counting ratio into the signed-bias formula. -/
theorem vectorColumnLaw_residual_ratio {n : ℕ} (k : ι → ℕ) (hk : ∀ j, k j ≤ n)
    (ask : List (ι → Bool) → Fin n) (past rows : List (ι → Bool))
    (hpos : ∃ S ∈ {S | vectorRowAnswers ask S past rows.length = rows},
      S ∈ (vectorColumnLaw Finset.univ k (by simpa using hk)).support)
    (m : ℝ) (theta : ι → ℝ) (hbalance : ∀ j, 2 * (k j : ℝ) = n + m * theta j) (j : ι) :
    ((k j - (vectorPositiveLabels ask past rows j).card : ℕ) : ℝ) /
      (Finset.univ \ (vectorPositiveLabels ask past rows j ∪ vectorNegativeLabels ask past rows j)).card =
      nextSignProbability n m (vectorHistorySize ask past rows) (vectorHistorySum ask past rows j) (theta j) := by
  let P := vectorPositiveLabels ask past rows j
  let N := vectorNegativeLabels ask past rows j
  obtain ⟨S, hS⟩ := vectorColumnLaw_history_feasible _ _ _ _ _ _ hpos j
  obtain ⟨hmem, hc⟩ := Finset.mem_filter.mp hS
  obtain ⟨hP, hPN, hPk, hrem⟩ := compatibleColumn_feasible _ P N S (k j) hmem hc
  have hd : (P ∪ N).card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ (P ∪ N))
  have hsum : ((P ∪ N).card : ℝ) = (P.card : ℝ) + N.card := by
    exact_mod_cast Finset.card_union_of_disjoint hPN
  have hsize : vectorHistorySize ask past rows = (P ∪ N).card :=
    congrArg Finset.card (vectorLabels_union ask past rows j).symm
  change ((k j - P.card : ℕ) : ℝ) / (Finset.univ \ (P ∪ N)).card = _
  rw [Finset.card_sdiff (Finset.subset_univ _)]
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_sub hPk, Nat.cast_sub hd]
  unfold nextSignProbability
  rw [hsize]
  change ((k j : ℝ) - P.card) / ((n : ℝ) - (P ∪ N).card) =
    ((n : ℝ) + m * theta j - (P ∪ N).card - ((P.card : ℝ) - N.card)) /
      (2 * ((n : ℝ) - (P ∪ N).card))
  have hnum : (n : ℝ) + m * theta j - (P ∪ N).card - ((P.card : ℝ) - N.card) =
      2 * ((k j : ℝ) - P.card) := by linarith [hbalance j]
  rw [hnum, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]

theorem vectorColumnLaw_next_row_mass_signed {n : ℕ} (k : ι → ℕ) (hk : ∀ j, k j ≤ n)
    (ask : List (ι → Bool) → Fin n) (past rows : List (ι → Bool))
    (hpos : ∃ S ∈ {S | vectorRowAnswers ask S past rows.length = rows},
      S ∈ (vectorColumnLaw Finset.univ k (by simpa using hk)).support)
    (i : Fin n) (hi : i ∉ vectorQueriedLabels ask past rows)
    (m : ℝ) (theta : ι → ℝ) (hbalance : ∀ j, 2 * (k j : ℝ) = n + m * theta j)
    (b : ι → Bool) :
    ((((vectorColumnLaw Finset.univ k (by simpa using hk)).filter
      {S | vectorRowAnswers ask S past rows.length = rows} hpos).map
        (fun S j => decide (i ∈ S j))) b).toReal =
      finiteProductWeight (fun j => bitWeight
        (nextSignProbability n m (vectorHistorySize ask past rows) (vectorHistorySum ask past rows j) (theta j))) b := by
  rw [vectorColumnLaw_next_row_mass _ _ _ _ _ _ hpos i
    (fun j => by simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, vectorLabels_union] using hi)]
  congr 1
  funext j
  rw [vectorColumnLaw_residual_ratio k hk ask past rows hpos m theta hbalance j]

end FullJet
