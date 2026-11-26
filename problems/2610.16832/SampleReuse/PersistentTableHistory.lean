import SampleReuse.DisclosureEntropy
import SecondOrder.FiniteCoordinateResampling

/-! Deterministic histories produced by a fixed, preallocated reusable table. -/

open SecondOrder
open scoped Classical
namespace SampleReuse
noncomputable section
variable {S Key A : Type}

def tableHistory (query : ∀ n, FiniteHistory S A n → Key)
    (s : S) (table : Key → A) : (n : ℕ) → FiniteHistory S A n
  | 0 => s
  | n + 1 => let h := tableHistory query s table n; (h, table (query n h))

/-- Every cached answer is the value stored in the original sampled table. -/
theorem tableHistory_cache_consistent (query : ∀ n, FiniteHistory S A n → Key)
    (s : S) (table : Key → A) :
    ∀ n key a, disclosureCache query n (tableHistory query s table n) key = some a → table key = a := by
  intro n
  induction n with
  | zero => intro key a ha; simp [disclosureCache] at ha
  | succ n ih =>
    intro key a ha
    by_cases hk : key = query n (tableHistory query s table n)
    · subst key
      simpa only [tableHistory, disclosureCache, Function.update_self, Option.some.injEq] using ha
    · simp only [tableHistory, disclosureCache, Function.update_of_ne hk] at ha
      exact ih key a ha

/-- Changing an undisclosed table coordinate leaves the entire past unchanged.
No restriction is imposed on adaptive revisits of already disclosed keys. -/
theorem tableHistory_update_unseen (query : ∀ n, FiniteHistory S A n → Key)
    (s : S) (table : Key → A) : ∀ n key,
    disclosureCache query n (tableHistory query s table n) key = none →
    ∀ a, tableHistory query s (Function.update table key a) n = tableHistory query s table n := by
  intro n
  induction n with
  | zero => intro key _ a; rfl
  | succ n ih =>
    intro key hu a
    have hk : key ≠ query n (tableHistory query s table n) := by
      intro he
      subst key
      simp [tableHistory, disclosureCache] at hu
    have hp : disclosureCache query n (tableHistory query s table n) key = none := by
      simpa only [tableHistory, disclosureCache, Function.update_of_ne hk] using hu
    change (tableHistory query s (Function.update table key a) n,
      Function.update table key a (query n (tableHistory query s (Function.update table key a) n))) =
      (tableHistory query s table n, table (query n (tableHistory query s table n)))
    rw [ih key hp a, Function.update_of_ne (Ne.symm hk)]

/-- The event of any history whose cache omits key k is invariant under
resampling k, including histories of zero probability. -/
theorem tableHistory_event_update_unseen (query : ∀ n, FiniteHistory S A n → Key)
    (s : S) (table : Key → A) (n : ℕ) (h : FiniteHistory S A n)
    (key : Key) (hu : disclosureCache query n h key = none) (a : A) :
    tableHistory query s (Function.update table key a) n = h ↔ tableHistory query s table n = h := by
  constructor
  · intro hh
    have hnone : disclosureCache query n (tableHistory query s (Function.update table key a) n) key = none := by
      rw [hh]
      exact hu
    have he := tableHistory_update_unseen query s (Function.update table key a) n key hnone (table key)
    have hupt : Function.update (Function.update table key a) key (table key) = table := by
      funext j
      by_cases hj : j = key
      · subst j; simp
      · simp [Function.update_of_ne hj]
    simpa only [hupt] using he.trans hh
  · intro hh
    have hnone : disclosureCache query n (tableHistory query s table n) key = none := by rw [hh]; exact hu
    exact (tableHistory_update_unseen query s table n key hnone a).trans hh

variable [Fintype Key] [Fintype A]

/-- Deferred decisions for one undisclosed table coordinate. This equality
is under the actual product table law, not an independence assumption. -/
theorem tableHistory_fresh_coordinate_mean
    (query : ∀ n, FiniteHistory S A n → Key) (p : Key → PMF A) (s : S)
    (n : ℕ) (h : FiniteHistory S A n) (key : Key)
    (hu : disclosureCache query n h key = none) (F : A → ℝ) :
    pmfMean (finitePiPMF p) (fun table => if tableHistory query s table n = h then F (table key) else 0) =
      pmfMean (finitePiPMF p) (fun table => if tableHistory query s table n = h then pmfMean (p key) F else 0) := by
  rw [← finitePiPMF_resample_mean p key]
  apply pmfMean_congr
  intro table
  simp only [tableHistory_event_update_unseen query s table n h key hu, Function.update_self]
  by_cases hh : tableHistory query s table n = h
  · simp only [if_pos hh]
  · simp only [if_neg hh, pmfMean_const]

end
end SampleReuse
