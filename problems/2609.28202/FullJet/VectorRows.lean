import FullJet.AdaptiveRows
import FullJet.UniformProduct

open scoped BigOperators ENNReal

namespace FullJet

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]

/-- Complete row answers. The selected label may depend on every coordinate
of every previous answer. -/
def vectorRowAnswers (ask : List (ι → Bool) → α) (S : ι → Finset α)
    (past : List (ι → Bool)) : ℕ → List (ι → Bool)
  | 0 => []
  | q + 1 =>
    let b := fun j => decide (ask past ∈ S j)
    b :: vectorRowAnswers ask S (past ++ [b]) q

def vectorPositiveLabels (ask : List (ι → Bool) → α) (past : List (ι → Bool)) :
    List (ι → Bool) → ι → Finset α
  | [], _ => ∅
  | b :: bs, j =>
    let P := vectorPositiveLabels ask (past ++ [b]) bs j
    if b j then insert (ask past) P else P

def vectorNegativeLabels (ask : List (ι → Bool) → α) (past : List (ι → Bool)) :
    List (ι → Bool) → ι → Finset α
  | [], _ => ∅
  | b :: bs, j =>
    let N := vectorNegativeLabels ask (past ++ [b]) bs j
    if b j then N else insert (ask past) N

theorem vectorCompatible_cons (ask : List (ι → Bool) → α) (S : ι → Finset α)
    (past : List (ι → Bool)) (b : ι → Bool) (bs : List (ι → Bool)) (j : ι) :
    compatibleColumn (vectorPositiveLabels ask past (b :: bs) j)
      (vectorNegativeLabels ask past (b :: bs) j) (S j) ↔
    decide (ask past ∈ S j) = b j ∧
      compatibleColumn (vectorPositiveLabels ask (past ++ [b]) bs j)
        (vectorNegativeLabels ask (past ++ [b]) bs j) (S j) := by
  cases hb : b j <;> simp [vectorPositiveLabels, vectorNegativeLabels, hb,
    compatibleColumn, Finset.disjoint_insert_left, Finset.insert_subset_iff] <;> tauto

/-- Fixing a full adaptive transcript converts its event into a Cartesian
product of column constraints, despite the shared adaptive choice of labels. -/
theorem vectorRowAnswers_eq_iff (ask : List (ι → Bool) → α) (S : ι → Finset α)
    (past rows : List (ι → Bool)) :
    vectorRowAnswers ask S past rows.length = rows ↔
      ∀ j, compatibleColumn (vectorPositiveLabels ask past rows j)
        (vectorNegativeLabels ask past rows j) (S j) := by
  induction rows generalizing past with
  | nil => simp [vectorRowAnswers, vectorPositiveLabels, vectorNegativeLabels, compatibleColumn]
  | cons b bs ih =>
    simp only [List.length_cons, vectorRowAnswers, List.cons.injEq]
    constructor
    · rintro ⟨hfirst, htail⟩
      rw [hfirst] at htail
      have hc := (ih (past ++ [b])).mp htail
      intro j
      exact (vectorCompatible_cons ask S past b bs j).mpr ⟨congrFun hfirst j, hc j⟩
    · intro hc
      have hfirst : (fun j => decide (ask past ∈ S j)) = b :=
        funext fun j => ((vectorCompatible_cons ask S past b bs j).mp (hc j)).1
      refine ⟨hfirst, ?_⟩
      rw [hfirst]
      exact (ih (past ++ [b])).mpr fun j =>
        ((vectorCompatible_cons ask S past b bs j).mp (hc j)).2

/-- Independent fixed-size columns, allowing a different signed bias in each
coordinate once the hidden sign vector is fixed. -/
noncomputable def vectorColumnLaw (U : Finset α) (k : ι → ℕ) (hk : ∀ j, k j ≤ U.card) :
    PMF (ι → Finset α) :=
  uniformPi (fun j => U.powersetCard (k j)) (fun j => Finset.powersetCard_nonempty.mpr (hk j))

def compatibleColumnSamples (U : Finset α) (k : ι → ℕ)
    (ask : List (ι → Bool) → α) (past rows : List (ι → Bool)) (j : ι) : Finset (Finset α) :=
  (U.powersetCard (k j)).filter
    (compatibleColumn (vectorPositiveLabels ask past rows j) (vectorNegativeLabels ask past rows j))

theorem vectorColumnLaw_history_feasible (U : Finset α) (k : ι → ℕ) (hk : ∀ j, k j ≤ U.card)
    (ask : List (ι → Bool) → α) (past rows : List (ι → Bool))
    (hpos : ∃ S ∈ {S | vectorRowAnswers ask S past rows.length = rows},
      S ∈ (vectorColumnLaw U k hk).support) :
    ∀ j, (compatibleColumnSamples U k ask past rows j).Nonempty := by
  obtain ⟨S, hrows, hS⟩ := hpos
  have hmem : S ∈ Fintype.piFinset (fun j => U.powersetCard (k j)) := by
    simpa only [vectorColumnLaw, uniformPi, PMF.mem_support_uniformOfFinset_iff] using hS
  intro j
  exact ⟨S j, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hmem j,
    (vectorRowAnswers_eq_iff ask S past rows).mp hrows j⟩⟩

/-- The conditional law of the whole table after an adaptive full-row history
is a product of uniform compatible-column laws. -/
theorem vectorColumnLaw_condition_history (U : Finset α) (k : ι → ℕ) (hk : ∀ j, k j ≤ U.card)
    (ask : List (ι → Bool) → α) (past rows : List (ι → Bool))
    (hpos : ∃ S ∈ {S | vectorRowAnswers ask S past rows.length = rows},
      S ∈ (vectorColumnLaw U k hk).support) :
    (vectorColumnLaw U k hk).filter {S | vectorRowAnswers ask S past rows.length = rows} hpos =
      uniformPi (compatibleColumnSamples U k ask past rows)
        (vectorColumnLaw_history_feasible U k hk ask past rows hpos) := by
  let A : ι → Set (Finset α) := fun j =>
    {S | compatibleColumn (vectorPositiveLabels ask past rows j) (vectorNegativeLabels ask past rows j) S}
  have hset : {S | vectorRowAnswers ask S past rows.length = rows} =
      {S | ∀ j, S j ∈ A j} := by
    ext S
    exact vectorRowAnswers_eq_iff ask S past rows
  have hpos' : ∃ S ∈ {S | ∀ j, S j ∈ A j}, S ∈ (vectorColumnLaw U k hk).support := by
    rwa [← hset]
  have hA := vectorColumnLaw_history_feasible U k hk ask past rows hpos
  convert uniformPi_condition_rect (fun j => U.powersetCard (k j))
    (fun j => Finset.powersetCard_nonempty.mpr (hk j)) A hA hpos' using 1
  congr 1

/-- Conditional probabilities of coordinatewise events factor after arbitrary
adaptive full-row observations. -/
theorem vectorColumnLaw_conditional_rect_probability (U : Finset α) (k : ι → ℕ)
    (hk : ∀ j, k j ≤ U.card) (ask : List (ι → Bool) → α) (past rows : List (ι → Bool))
    (hpos : ∃ S ∈ {S | vectorRowAnswers ask S past rows.length = rows},
      S ∈ (vectorColumnLaw U k hk).support) (B : ι → Set (Finset α)) :
    (((vectorColumnLaw U k hk).filter {S | vectorRowAnswers ask S past rows.length = rows} hpos).toOuterMeasure
      {S | ∀ j, S j ∈ B j}).toReal =
      ∏ j, ((PMF.uniformOfFinset (compatibleColumnSamples U k ask past rows j)
        (vectorColumnLaw_history_feasible U k hk ask past rows hpos j)).toOuterMeasure (B j)).toReal := by
  rw [vectorColumnLaw_condition_history]
  exact uniformPi_rect_probability _ _ _

theorem vectorColumnLaw_conditional_coordinate_probability (U : Finset α) (k : ι → ℕ)
    (hk : ∀ j, k j ≤ U.card) (ask : List (ι → Bool) → α) (past rows : List (ι → Bool))
    (hpos : ∃ S ∈ {S | vectorRowAnswers ask S past rows.length = rows},
      S ∈ (vectorColumnLaw U k hk).support) (j : ι) (B : Set (Finset α)) :
    (((vectorColumnLaw U k hk).filter {S | vectorRowAnswers ask S past rows.length = rows} hpos).toOuterMeasure
      {S | S j ∈ B}).toReal =
      ((PMF.uniformOfFinset (compatibleColumnSamples U k ask past rows j)
        (vectorColumnLaw_history_feasible U k hk ask past rows hpos j)).toOuterMeasure B).toReal := by
  rw [vectorColumnLaw_condition_history]
  exact uniformPi_coordinate_probability _ _ _ _

/-- A column's residual fixed-size law remains exact even when queries use the
entire vector history, not merely that column's answers. -/
theorem compatibleColumnSamples_residual (U : Finset α) (k : ι → ℕ)
    (ask : List (ι → Bool) → α) (past rows : List (ι → Bool)) (j : ι)
    (hA : (compatibleColumnSamples U k ask past rows j).Nonempty) :
    ∃ hrem : k j - (vectorPositiveLabels ask past rows j).card ≤
        (U \ (vectorPositiveLabels ask past rows j ∪ vectorNegativeLabels ask past rows j)).card,
    PMF.uniformOfFinset (compatibleColumnSamples U k ask past rows j) hA =
      (fixedSizeLaw (U \ (vectorPositiveLabels ask past rows j ∪ vectorNegativeLabels ask past rows j))
        (k j - (vectorPositiveLabels ask past rows j).card) hrem).map
          (vectorPositiveLabels ask past rows j ∪ ·) := by
  let P := vectorPositiveLabels ask past rows j
  let N := vectorNegativeLabels ask past rows j
  obtain ⟨S, hS⟩ := hA
  obtain ⟨hmem, hc⟩ := Finset.mem_filter.mp hS
  obtain ⟨hP, hPN, hPk, hrem⟩ := compatibleColumn_feasible U P N S (k j) hmem hc
  refine ⟨hrem, ?_⟩
  have hR := Finset.powersetCard_nonempty.mpr hrem
  trans PMF.uniformOfFinset (((U \ (P ∪ N)).powersetCard (k j - P.card)).image (P ∪ ·))
    (hR.image (P ∪ ·))
  · congr 1
    exact powersetCard_filter_compatible U P N (k j) hP hPN hPk
  · exact (uniformOfFinset_map_injOn _ hR _ (union_injOn_residual U P N _)).symm

/-- Exact next-coordinate probability for a genuinely adaptive full-row
protocol, with no cross-coordinate restriction on the querying strategy. -/
theorem vectorColumnLaw_next_probability (U : Finset α) (k : ι → ℕ)
    (hk : ∀ j, k j ≤ U.card) (ask : List (ι → Bool) → α) (past rows : List (ι → Bool))
    (hpos : ∃ S ∈ {S | vectorRowAnswers ask S past rows.length = rows},
      S ∈ (vectorColumnLaw U k hk).support)
    (j : ι) (i : α)
    (hi : i ∈ U \ (vectorPositiveLabels ask past rows j ∪ vectorNegativeLabels ask past rows j)) :
    (((vectorColumnLaw U k hk).filter {S | vectorRowAnswers ask S past rows.length = rows} hpos).toOuterMeasure
      {S | i ∈ S j}).toReal =
      ((k j - (vectorPositiveLabels ask past rows j).card : ℕ) : ℝ) /
        (U \ (vectorPositiveLabels ask past rows j ∪ vectorNegativeLabels ask past rows j)).card := by
  have hcoord := vectorColumnLaw_conditional_coordinate_probability U k hk ask past rows hpos j {S | i ∈ S}
  simp only [Set.mem_setOf_eq] at hcoord
  rw [hcoord]
  obtain ⟨hrem, heq⟩ := compatibleColumnSamples_residual U k ask past rows j
    (vectorColumnLaw_history_feasible U k hk ask past rows hpos j)
  rw [heq, PMF.toOuterMeasure_map_apply]
  have hiP : i ∉ vectorPositiveLabels ask past rows j := fun h =>
    (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ h)
  have hset : (fun S => vectorPositiveLabels ask past rows j ∪ S) ⁻¹' {S | i ∈ S} = {S | i ∈ S} := by
    ext S
    simp [hiP]
  rw [hset]
  exact fixedSizeLaw_present_probability _ _ i hi hrem

end FullJet
