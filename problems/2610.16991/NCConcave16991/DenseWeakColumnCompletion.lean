import NCConcave16991.DenseWeakUniformCondition
import Mathlib.Data.Finset.Image

/-! # Actual completions of a fixed sign-column observation -/

noncomputable section

open Set

namespace NCConcave16991.DenseWeakHiding

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev UnseenRows (R : Finset I) := {i : I // i ∉ R}
abbrev ObservedColumn (k : ℕ) (R B : Finset I) :=
  {A : PositiveColumn I k // A.val ∩ R = B}

def remainingColumn {k : ℕ} {R B : Finset I} (A : ObservedColumn k R B) :
    PositiveColumn (UnseenRows R) (k - B.card) := by
  refine ⟨A.val.val.subtype (fun i ↦ i ∉ R), ?_⟩
  rw [Finset.card_subtype]
  have he : A.val.val.filter (fun i ↦ i ∉ R) = A.val.val \ R := by ext i; simp
  rw [he, Finset.card_sdiff, Finset.inter_comm R A.val.val, A.property, A.val.property]

theorem remainingColumn_mem {k : ℕ} {R B : Finset I} (A : ObservedColumn k R B)
    (i : UnseenRows R) : i ∈ (remainingColumn A).val ↔ i.val ∈ A.val.val :=
  Finset.mem_subtype

def completeColumn {k : ℕ} {R B : Finset I} (hB : B ⊆ R) (hBk : B.card ≤ k)
    (C : PositiveColumn (UnseenRows R) (k - B.card)) : ObservedColumn k R B := by
  let F : Finset I := C.val.map (Function.Embedding.subtype (fun i ↦ i ∉ R))
  have hd : Disjoint B F := by
    apply Finset.disjoint_left.mpr
    intro i hi hf
    rcases Finset.mem_map.mp hf with ⟨j, hj, rfl⟩
    exact j.property (hB hi)
  have hc : (B ∪ F).card = k := by
    rw [Finset.card_union_of_disjoint hd]
    dsimp [F]
    rw [Finset.card_map, C.property]
    omega
  refine ⟨⟨B ∪ F, hc⟩, ?_⟩
  change (B ∪ F) ∩ R = B
  ext i
  constructor
  · intro hi
    obtain ⟨hi, hRi⟩ := Finset.mem_inter.mp hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hi
    · rcases Finset.mem_map.mp hi with ⟨j, hj, rfl⟩
      exact (j.property hRi).elim
  · intro hi
    exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hi, hB hi⟩

theorem complete_remainingColumn {k : ℕ} {R B : Finset I}
    (hB : B ⊆ R) (hBk : B.card ≤ k) (A : ObservedColumn k R B) :
    completeColumn hB hBk (remainingColumn A) = A := by
  apply Subtype.ext
  apply Subtype.ext
  ext i
  change i ∈ B ∪ ((A.val.val.subtype (fun i ↦ i ∉ R)).map (Function.Embedding.subtype _)) ↔
    i ∈ A.val.val
  rw [Finset.subtype_map]
  by_cases hi : i ∈ R
  · have hiff : i ∈ B ↔ i ∈ A.val.val := by
      have heq := congrArg (fun S : Finset I ↦ i ∈ S) A.property
      constructor
      · intro h
        exact (Finset.mem_inter.mp (Eq.mpr heq h)).1
      · intro h
        exact Eq.mp heq (Finset.mem_inter.mpr ⟨h, hi⟩)
    simpa [hi] using hiff
  · have hbnot : i ∉ B := fun h ↦ hi (hB h)
    simp [hi, hbnot]

theorem remaining_completeColumn {k : ℕ} {R B : Finset I}
    (hB : B ⊆ R) (hBk : B.card ≤ k) (C : PositiveColumn (UnseenRows R) (k - B.card)) :
    remainingColumn (completeColumn hB hBk C) = C := by
  apply Subtype.ext
  ext i
  rw [remainingColumn_mem]
  change i.val ∈ B ∪ C.val.map (Function.Embedding.subtype (fun i ↦ i ∉ R)) ↔ i ∈ C.val
  have hbnot : i.val ∉ B := fun h ↦ i.property (hB h)
  simp only [Finset.mem_union, hbnot, false_or, Finset.mem_map]
  constructor
  · rintro ⟨j, hj, hji⟩
    have he : j = i := Subtype.ext hji
    simpa only [he] using hj
  · intro hi
    exact ⟨i, hi, rfl⟩

/-- The observation fibre is exactly the smaller fixed-cardinality column
on the actual unread row set. Both maps are explicitly constructed. -/
def columnCompletionEquiv {k : ℕ} {R B : Finset I} (hB : B ⊆ R) (hBk : B.card ≤ k) :
    ObservedColumn k R B ≃ PositiveColumn (UnseenRows R) (k - B.card) where
  toFun := remainingColumn
  invFun := completeColumn hB hBk
  left_inv := complete_remainingColumn hB hBk
  right_inv := remaining_completeColumn hB hBk

end NCConcave16991.DenseWeakHiding
