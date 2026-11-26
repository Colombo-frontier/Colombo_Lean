import SampleReuse.PersistentHandleNormalization
import SampleReuse.PersistentTableLaw

open SecondOrder
open scoped Classical
namespace SampleReuse
noncomputable section
variable {S H A : Type}

def queriedLabels (query : ∀ n, FiniteHistory S A n → H) :
    (n : ℕ) → FiniteHistory S A n → List H
  | 0, _ => []
  | n+1,h => queriedLabels query n h.1 ++ [query n h.1]

theorem queriedLabels_length (query : ∀ n, FiniteHistory S A n → H) :
    ∀ n h, (queriedLabels query n h).length = n := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih => intro h; simp only [queriedLabels,List.length_append,List.length_singleton,ih]

def normalizeHandleQuery (N : ℕ) (query : ∀ n, FiniteHistory S A n → H)
    (n : ℕ) (h : FiniteHistory S A n) : Fin (N+1) :=
  handleSlot N (queriedLabels query n h) (query n h)

theorem normalizeHandleQuery_le (N : ℕ) (query : ∀ n, FiniteHistory S A n → H)
    (n : ℕ) (h : FiniteHistory S A n) : (normalizeHandleQuery N query n h).val ≤ n := by
  exact (min_le_left _ _).trans (List.idxOf_le_length.trans (queriedLabels_length query n h).le)

theorem disclosureCache_none_of_unseen (query : ∀ n, FiniteHistory S A n → H) :
    ∀ n h k, k ∉ queriedLabels query n h → disclosureCache query n h k = none := by
  intro n
  induction n with
  | zero => intro h k _; rfl
  | succ n ih =>
    intro h k hk
    have hp : k ∉ queriedLabels query n h.1 := fun hp => hk (List.mem_append_left _ hp)
    have hn : k ≠ query n h.1 := fun he => hk (List.mem_append_right _ (by simp [he]))
    simpa only [disclosureCache,Function.update_of_ne hn] using ih h.1 k hp

theorem normalizedCache_unused (N : ℕ) (query : ∀ n, FiniteHistory S A n → H) :
    ∀ n h i, n ≤ i.val → disclosureCache (normalizeHandleQuery N query) n h i = none := by
  letI : DecidableEq (Fin (N+1)) := Classical.decEq _
  intro n
  induction n with
  | zero => intro h i _; rfl
  | succ n ih =>
    intro h i hi
    have hq := normalizeHandleQuery_le N query n h.1
    have hn : i ≠ normalizeHandleQuery N query n h.1 := by intro he; rw [he] at hi; omega
    change Function.update (disclosureCache (normalizeHandleQuery N query) n h.1)
      (normalizeHandleQuery N query n h.1) (some h.2) i = none
    rw [Function.update_of_ne hn]
    exact ih h.1 i (by omega)

theorem normalizedCache_seen (N : ℕ) (query : ∀ n, FiniteHistory S A n → H) :
    ∀ n, n ≤ N → ∀ h k, k ∈ queriedLabels query n h →
      disclosureCache (normalizeHandleQuery N query) n h (handleSlot N (queriedLabels query n h) k) =
        disclosureCache query n h k := by
  letI : DecidableEq (Fin (N+1)) := Classical.decEq _
  intro n
  induction n with
  | zero => intro _ h k hk; simp [queriedLabels] at hk
  | succ n ih =>
    intro hn h k hk
    have hlen : (queriedLabels query n h.1).length ≤ N := by rw [queriedLabels_length]; omega
    by_cases he : k = query n h.1
    · subst k
      change Function.update (disclosureCache (normalizeHandleQuery N query) n h.1)
        (handleSlot N (queriedLabels query n h.1) (query n h.1)) (some h.2)
        (handleSlot N (queriedLabels query n h.1 ++ [query n h.1]) (query n h.1)) = _
      rw [handleSlot_append_self,Function.update_self]
      simp only [disclosureCache,Function.update_self]
    · have hp : k ∈ queriedLabels query n h.1 := by
        simpa only [queriedLabels,List.mem_append,List.mem_singleton,he,or_false] using hk
      have hi : handleSlot N (queriedLabels query n h.1) k ≠ normalizeHandleQuery N query n h.1 := by
        exact fun hi => he ((handleSlot_eq_iff N _ _ _ hlen hp).mp hi)
      change Function.update (disclosureCache (normalizeHandleQuery N query) n h.1)
        (normalizeHandleQuery N query n h.1) (some h.2)
        (handleSlot N (queriedLabels query n h.1 ++ [query n h.1]) k) = _
      rw [handleSlot_reused N _ _ k hp,Function.update_of_ne hi]
      simp only [disclosureCache,Function.update_of_ne he]
      exact ih (by omega) h.1 k hp

/-- The cached value agrees even for inconsistent zero-probability histories.
Thus the fresh/reused transition kernels agree without a support premise. -/
theorem normalizedCache_current (N : ℕ) (query : ∀ n, FiniteHistory S A n → H)
    (n : ℕ) (hn : n ≤ N) (h : FiniteHistory S A n) :
    disclosureCache (normalizeHandleQuery N query) n h (normalizeHandleQuery N query n h) =
      disclosureCache query n h (query n h) := by
  by_cases hk : query n h ∈ queriedLabels query n h
  · exact normalizedCache_seen N query n hn h _ hk
  · rw [disclosureCache_none_of_unseen query n h _ hk]
    apply normalizedCache_unused
    exact (handleSlot_fresh N _ _ (by rw [queriedLabels_length]; exact hn) hk).ge.trans'
      (queriedLabels_length query n h).ge

/-- Arbitrary labels and at most N+1 finite slots have identical lazy
transcript laws for iid full samples. The original label type is unrestricted. -/
theorem normalized_lazy_law (N : ℕ) (query : ∀ n, FiniteHistory S A n → H)
    (p : PMF A) (s : S) : ∀ n, n ≤ N →
    lazyDisclosurePMF (normalizeHandleQuery N query) (fun _ => p) s n =
      lazyDisclosurePMF query (fun _ => p) s n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    rw [lazyDisclosurePMF,lazyDisclosurePMF,ih (by omega)]
    congr 1
    funext h
    rw [normalizedCache_current N query n (by omega) h]

end
end SampleReuse
