import SampleReuse.PersistentStopCoupling

/-! Deterministic history-event and response-count identities for a fixed
reusable table. They include the terminal test without another response. -/

open SecondOrder
open scoped Classical
namespace SampleReuse
noncomputable section
variable {S A Key : Type}

theorem tableHistory_survival (query : ∀ n, FiniteHistory S A n → Key) (s : S) (table : Key → A)
    (safe : ∀ n, Set (FiniteHistory S A n)) : ∀ N,
    tableHistory query s table N ∈ kernelSurvivalSet safe N ↔
      ∀ t, t ≤ N → tableHistory query s table t ∈ safe t := by
  intro N
  induction N with
  | zero => simp only [kernelSurvivalSet, Nat.le_zero]; aesop
  | succ N ih =>
    change (tableHistory query s table (N + 1) ∈ safe (N + 1) ∧
      tableHistory query s table N ∈ kernelSurvivalSet safe N) ↔ _
    rw [ih]
    constructor
    · rintro ⟨ha, hb⟩ t ht
      by_cases he : t = N + 1
      · subst t; exact ha
      · exact hb t (by omega)
    · intro h; exact ⟨h _ le_rfl, fun t ht => h t (by omega)⟩

theorem tableHistory_before (query : ∀ n, FiniteHistory S A n → Key) (s : S) (table : Key → A)
    (safe : ∀ n, Set (FiniteHistory S A n)) (N : ℕ) :
    tableHistory query s table N ∈ kernelBeforeSet safe N ↔
      ∀ t, t < N → tableHistory query s table t ∈ safe t := by
  cases N with
  | zero => simp [kernelBeforeSet]
  | succ N =>
    change tableHistory query s table N ∈ kernelSurvivalSet safe N ↔ _
    rw [tableHistory_survival]
    exact forall_congr' (fun t => by simp only [Nat.lt_succ_iff])

theorem tableHistory_stopped_hit (query : ∀ n, FiniteHistory S A n → Key) (s : S) (table : Key → A)
    (safe hit : ∀ n, Set (FiniteHistory S A n)) : ∀ N t, t ≤ N →
    (∀ u, u < t → tableHistory query s table u ∈ safe u) →
    tableHistory query s table t ∈ hit t →
    tableHistory query s table N ∈ kernelStoppedHitSet safe hit N := by
  intro N
  induction N with
  | zero =>
    intro t ht _ hh
    have he : t = 0 := Nat.eq_zero_of_le_zero ht
    subst t
    exact hh
  | succ N ih =>
    intro t ht hs hh
    by_cases he : t = N + 1
    · subst t
      exact Or.inr ⟨(tableHistory_before query s table safe (N + 1)).mpr hs, hh⟩
    · exact Or.inl (ih t (by omega) hs hh)

def tableResponseCount (query : ∀ n, FiniteHistory S A n → Key) (target : Key → Prop)
    (s : S) (table : Key → A) : ℕ → ℕ
  | 0 => 0
  | n + 1 => tableResponseCount query target s table n +
      if target (query n (tableHistory query s table n)) then 1 else 0

theorem tableResponseCount_mono (query : ∀ n, FiniteHistory S A n → Key) (target : Key → Prop)
    (s : S) (table : Key → A) : Monotone (tableResponseCount query target s table) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Nat.le_add_right _ _

theorem kernelChargeCount_table_le (query : ∀ n, FiniteHistory S A n → Key) (target : Key → Prop)
    (s : S) (table : Key → A) (cap : ℕ) : ∀ n,
    kernelChargeCount (targetDisclosure query target) cap n (tableHistory query s table n) ≤
      tableResponseCount query target s table n := by
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    change (if kernelChargeCount (targetDisclosure query target) cap n (tableHistory query s table n) < cap ∧
        target (query n (tableHistory query s table n)) then
      kernelChargeCount (targetDisclosure query target) cap n (tableHistory query s table n) + 1 else
      kernelChargeCount (targetDisclosure query target) cap n (tableHistory query s table n)) ≤
      tableResponseCount query target s table n + if target (query n (tableHistory query s table n)) then 1 else 0
    by_cases hs : target (query n (tableHistory query s table n))
    · by_cases hc : kernelChargeCount (targetDisclosure query target) cap n (tableHistory query s table n) < cap
      · simp only [hs, hc, and_self, if_true]
        exact Nat.add_le_add_right ih 1
      · simp only [hs, hc, false_and, if_false, if_true]
        exact ih.trans (Nat.le_add_right _ _)
    · simp only [hs, and_false, if_false, Nat.add_zero]
      exact ih

end
end SampleReuse
