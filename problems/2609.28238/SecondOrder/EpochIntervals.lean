import SecondOrder.EpochMeasurability

open MeasureTheory
open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

/-- First time at or beyond epoch e, truncated at the actual physical
length N. Empty and unvisited epochs have equal consecutive boundaries. -/
def epochBoundary (N q : ℕ) (g : ℕ → Bool) (e : ℕ) : ℕ :=
  Nat.find (show ∃ t, N ≤ t ∨ e ≤ epochOfStep q g t from ⟨N,Or.inl le_rfl⟩)

theorem epochBoundary_le_cap (N q : ℕ) (g : ℕ → Bool) (e : ℕ) : epochBoundary N q g e ≤ N :=
  Nat.find_min' _ (Or.inl le_rfl)

theorem epochBoundary_le_iff (N q : ℕ) (g : ℕ → Bool) (e t : ℕ) :
    epochBoundary N q g e ≤ t ↔ N ≤ t ∨ e ≤ epochOfStep q g t := by
  constructor
  · intro ht
    have hs := Nat.find_spec (show ∃ t, N ≤ t ∨ e ≤ epochOfStep q g t from ⟨N,Or.inl le_rfl⟩)
    change N ≤ epochBoundary N q g e ∨ e ≤ epochOfStep q g (epochBoundary N q g e) at hs
    rcases hs with hn | he
    · exact Or.inl (hn.trans ht)
    · exact Or.inr (he.trans (epochOfStep_mono q g ht))
  · intro ht
    exact Nat.find_min' (show ∃ t, N ≤ t ∨ e ≤ epochOfStep q g t from ⟨N,Or.inl le_rfl⟩) ht

theorem epochBoundary_mono (N q : ℕ) (g : ℕ → Bool) : Monotone (epochBoundary N q g) := by
  intro e f hef
  apply (epochBoundary_le_iff N q g e _).mpr
  have hh := (epochBoundary_le_iff N q g f _).mp (le_refl _)
  exact hh.imp_right (fun h => hef.trans h)

@[simp] theorem epochBoundary_zero (N q : ℕ) (g : ℕ → Bool) : epochBoundary N q g 0 = 0 := by
  have hh := (epochBoundary_le_iff N q g 0 0).mpr (Or.inr (Nat.zero_le _))
  omega

theorem epochBoundary_last {N M : ℕ} (hNM : N ≤ M) (q : ℕ) (g : ℕ → Bool) :
    epochBoundary N q g M = N := by
  have hb := epochBoundary_le_cap N q g M
  have hh := (epochBoundary_le_iff N q g M _).mp (le_refl _)
  have hl := epochOfStep_le q g (epochBoundary N q g M)
  omega

def epochLength (N q : ℕ) (g : ℕ → Bool) (e : ℕ) : ℕ :=
  epochBoundary N q g (e+1)-epochBoundary N q g e

theorem epochLength_add_start (N q : ℕ) (g : ℕ → Bool) (e : ℕ) :
    epochBoundary N q g e+epochLength N q g e = epochBoundary N q g (e+1) := by
  have hh := epochBoundary_mono N q g (Nat.le_succ e)
  change epochBoundary N q g e ≤ epochBoundary N q g (e+1) at hh
  dsimp only [epochLength]
  omega

theorem epochLength_le_cap (N q : ℕ) (g : ℕ → Bool) (e : ℕ) : epochLength N q g e ≤ N :=
  (Nat.sub_le _ _).trans (epochBoundary_le_cap N q g (e+1))

/-- The actual epoch is exactly this half-open interval of physical moves. -/
theorem epoch_interval_iff (N q : ℕ) (g : ℕ → Bool) (e t : ℕ) :
    epochBoundary N q g e ≤ t ∧ t < epochBoundary N q g (e+1) ↔
      t < N ∧ epochOfStep q g t = e := by
  have hb := epochBoundary_le_cap N q g (e+1)
  have he := epochBoundary_le_iff N q g e t
  have hf := epochBoundary_le_iff N q g (e+1) t
  omega

theorem epoch_local_time {N q e k : ℕ} {g : ℕ → Bool} (hk : k < epochLength N q g e) :
    epochBoundary N q g e+k < N ∧
      epochOfStep q g (epochBoundary N q g e+k) = e := by
  apply (epoch_interval_iff N q g e _).mp
  have hh := epochLength_add_start N q g e
  omega

/-- The truncated boundary agrees with the restart clock whenever the
epoch contains the queried physical move. -/
theorem epochBoundary_eq_clock {N q e t : ℕ} (hq : 0 < q) {g : ℕ → Bool}
    (ht : t < N) (he : epochOfStep q g t = e) :
    epochBoundary N q g e = (epochClock q g t).start := by
  have hbe : epochBoundary N q g e ≤ t := (epochBoundary_le_iff N q g e t).mpr (Or.inr he.ge)
  have hs := (epochClock_invariant hq g t).2.2
  have hl := epochClock_start_same_epoch hq g t _ le_rfl hs
  have h1 : epochBoundary N q g e ≤ (epochClock q g t).start :=
    (epochBoundary_le_iff N q g e _).mpr (Or.inr (by omega))
  have hb := (epochBoundary_le_iff N q g e _).mp (le_refl _)
  have h2 : (epochClock q g t).start ≤ epochBoundary N q g e := by
    by_contra hh
    have hh' := epochClock_before_start hq g t _ (Nat.lt_of_not_ge hh)
    omega
  omega

theorem epoch_local_address {N q e k : ℕ} (hq : 0 < q) {g : ℕ → Bool}
    (hk : k < epochLength N q g e) :
    epochAddress q g (epochBoundary N q g e+k) = (e,k) := by
  have ht := epoch_local_time hk
  have hs := epochBoundary_eq_clock hq ht.1 ht.2
  simp only [epochAddress,ht.2,← hs,Nat.add_sub_cancel_left]

theorem sum_epochLength_upto (N q : ℕ) (g : ℕ → Bool) (R : ℕ) :
    (∑ e ∈ Finset.range R, epochLength N q g e) = epochBoundary N q g R := by
  induction R with
  | zero => simp
  | succ R ih => rw [Finset.sum_range_succ,ih,epochLength_add_start]

theorem sum_epochLength {N M : ℕ} (hNM : N ≤ M) (q : ℕ) (g : ℕ → Bool) :
    (∑ e : Fin M, epochLength N q g e.val) = N := by
  rw [Fin.sum_univ_eq_sum_range (epochLength N q g),sum_epochLength_upto,epochBoundary_last hNM]

theorem epochBoundary_measurable {A : Type*} [MeasurableSpace A] {q : ℕ} (hq : 0 < q)
    {N : A → ℕ} (hN : Measurable N) {g : A → ℕ → Bool}
    (hg : ∀ t, Measurable (fun a => g a t)) (e : ℕ) :
    Measurable (fun a => epochBoundary (N a) q (g a) e) := by
  apply measurable_find
  intro t
  have hz := (epochClockEncode_measurable.comp (epochClock_measurable q hg t)).fst
  change Measurable (fun a => (epochClock q (g a) t).number) at hz
  have hl : Measurable (fun a => epochOfStep q (g a) t) := by
    simpa only [epochClock_number hq] using hz
  exact (measurableSet_le hN measurable_const).union (measurableSet_le measurable_const hl)

theorem epochLength_measurable {A : Type*} [MeasurableSpace A] {q : ℕ} (hq : 0 < q)
    {N : A → ℕ} (hN : Measurable N) {g : A → ℕ → Bool}
    (hg : ∀ t, Measurable (fun a => g a t)) (e : ℕ) :
    Measurable (fun a => epochLength (N a) q (g a) e) :=
  (epochBoundary_measurable hq hN hg (e+1)).sub (epochBoundary_measurable hq hN hg e)

end
end SecondOrder
