import SecondOrder.EpochClock

open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

def epochSteps (M q : ℕ) (g : ℕ → Bool) (e : ℕ) : Finset (Fin M) :=
  Finset.univ.filter (fun k => epochOfStep q g k.val = e)

def epochGradientSteps (M q : ℕ) (g : ℕ → Bool) (e : ℕ) : Finset (Fin M) :=
  (epochSteps M q g e).filter (fun k => g k.val = true)

@[simp] theorem mem_epochSteps {M q e : ℕ} {g : ℕ → Bool} {k : Fin M} :
    k ∈ epochSteps M q g e ↔ epochOfStep q g k.val = e := by simp [epochSteps]

@[simp] theorem mem_epochGradientSteps {M q e : ℕ} {g : ℕ → Bool} {k : Fin M} :
    k ∈ epochGradientSteps M q g e ↔ epochOfStep q g k.val = e ∧ g k.val = true := by
  simp [epochGradientSteps]

theorem epochSteps_disjoint (M q : ℕ) (g : ℕ → Bool) {e f : ℕ} (hef : e ≠ f) :
    Disjoint (epochSteps M q g e) (epochSteps M q g f) := by
  apply Finset.disjoint_left.mpr
  intro k hk hl
  exact hef ((mem_epochSteps.mp hk).symm.trans (mem_epochSteps.mp hl))

/-- Epochs are intervals of physical moves, including the last gradient
move that causes the next reset. -/
theorem epochSteps_contiguous {M q e : ℕ} {g : ℕ → Bool} {i j k : Fin M}
    (hi : i ∈ epochSteps M q g e) (hk : k ∈ epochSteps M q g e) (hij : i ≤ j) (hjk : j ≤ k) :
    j ∈ epochSteps M q g e := by
  apply mem_epochSteps.mpr
  have h1 := epochOfStep_mono q g (show i.val ≤ j.val from hij)
  have h2 := epochOfStep_mono q g (show j.val ≤ k.val from hjk)
  rw [mem_epochSteps.mp hi] at h1
  rw [mem_epochSteps.mp hk] at h2
  omega

/-- At most q gradient moves lie in any one actual epoch. The proof maps
each such move injectively to its global gradient ordinal in [eq,(e+1)q). -/
theorem epochGradientSteps_card (M : ℕ) {q : ℕ} (hq : 0 < q) (g : ℕ → Bool) (e : ℕ) :
    (epochGradientSteps M q g e).card ≤ q := by
  have hh : (epochGradientSteps M q g e).card ≤ (Finset.Ico (e*q) ((e+1)*q)).card := by
    apply Finset.card_le_card_of_injOn (fun k => gradientCount g k.val)
    · intro k hk
      have he := (mem_epochGradientSteps.mp hk).1
      have hd := (Nat.div_eq_iff hq).mp he
      apply Finset.mem_Ico.mpr
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    · intro i hi j hj he
      change gradientCount g i.val = gradientCount g j.val at he
      have hi' := (mem_epochGradientSteps.mp hi).2
      have hj' := (mem_epochGradientSteps.mp hj).2
      apply Fin.ext
      rcases lt_trichotomy i.val j.val with hij | hij | hij
      · have hh := gradientCount_strict hij hi'
        omega
      · exact hij
      · have hh := gradientCount_strict hij hj'
        omega
  simpa [Nat.add_mul, Nat.add_sub_cancel_left] using hh

theorem epochLabel_lt (M q : ℕ) (g : ℕ → Bool) (k : Fin M) : epochOfStep q g k.val < M+1 :=
  (epochOfStep_le q g k.val).trans_lt (by omega)

/-- Every physical move is counted exactly once, without a separate
partition hypothesis. This identity also applies to path-energy charges. -/
theorem sum_epochSteps {V : Type*} [AddCommMonoid V] (M q : ℕ) (g : ℕ → Bool) (v : Fin M → V) :
    (∑ e : Fin (M+1), ∑ k ∈ epochSteps M q g e.val, v k) = ∑ k, v k := by
  simp only [epochSteps, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  let e : Fin (M+1) := ⟨epochOfStep q g k.val,epochLabel_lt M q g k⟩
  rw [Finset.sum_eq_single e]
  · simp [e]
  · intro j hj hje
    have hne : epochOfStep q g k.val ≠ j.val := by
      intro h
      exact hje (Fin.ext h.symm)
    simp [hne]
  · simp

theorem sum_epochSteps_card (M q : ℕ) (g : ℕ → Bool) :
    (∑ e : Fin (M+1), (epochSteps M q g e.val).card) = M := by
  simpa using sum_epochSteps M q g (fun _ => (1 : ℕ))

theorem epoch_drift_support {E : Type*} [Zero E] (M : ℕ) {q : ℕ} (hq : 0 < q)
    (g : ℕ → Bool) (a : Fin M → E) (ha : ∀ k, a k ≠ 0 → g k.val = true) (e : ℕ) :
    ((epochSteps M q g e).filter (fun k => a k ≠ 0)).card ≤ q := by
  refine (Finset.card_le_card ?_).trans (epochGradientSteps_card M hq g e)
  intro k hk
  obtain ⟨hk,ha'⟩ := Finset.mem_filter.mp hk
  exact mem_epochGradientSteps.mpr ⟨mem_epochSteps.mp hk,ha k ha'⟩

def epochAnchorCount (q : ℕ) (g : ℕ → Bool) (N : ℕ) : ℕ := (epochClock q g N).number+1

def epochReset (q : ℕ) (g : ℕ → Bool) (t : ℕ) : Bool :=
  g t && decide ((epochClock q g t).gradients+1 = q)

theorem epochReset_count (q : ℕ) (g : ℕ → Bool) (N : ℕ) :
    gradientCount (epochReset q g) N = (epochClock q g N).number := by
  induction N with
  | zero => rfl
  | succ n ih =>
    cases hg : g n
    · simp [gradientCount,epochReset,epochClock,epochClockStep,hg,ih]
    · by_cases he : (epochClock q g n).gradients+1 = q <;>
        simp [gradientCount,epochReset,epochClock,epochClockStep,hg,he,ih]

theorem epochAnchorCount_resets (q : ℕ) (g : ℕ → Bool) (N : ℕ) :
    epochAnchorCount q g N = 1+∑ t ∈ Finset.range N, if epochReset q g t then 1 else 0 := by
  rw [← gradientCount_eq_sum,epochReset_count]
  exact Nat.add_comm _ _

theorem epochAnchorCount_eq {q : ℕ} (hq : 0 < q) (g : ℕ → Bool) (N : ℕ) :
    epochAnchorCount q g N = 1+gradientCount g N/q := by
  simp [epochAnchorCount,epochClock_number hq,epochOfStep,Nat.add_comm]

theorem epochAnchorCount_bound {q : ℕ} (hq : 0 < q) (g : ℕ → Bool) (N : ℕ) :
    (epochAnchorCount q g N : ℝ) ≤ 1+(gradientCount g N : ℝ)/(q : ℝ) := by
  rw [epochAnchorCount_eq hq]
  push_cast
  apply add_le_add_left
  apply (le_div_iff₀ (Nat.cast_pos.mpr hq)).mpr
  exact_mod_cast Nat.div_mul_le_self (gradientCount g N) q

end
end SecondOrder
