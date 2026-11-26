import SecondOrder.BinaryNodes

open scoped Classical BigOperators

namespace SecondOrder

structure EpochClock where
  number : ℕ
  gradients : ℕ
  start : ℕ
  deriving DecidableEq

def gradientCount (g : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | t+1 => gradientCount g t+if g t then 1 else 0

/-- The q-th gradient move belongs to the old epoch. The new epoch and
its fresh anchor begin at the endpoint of that move. Curvature moves do
not advance the gradient counter or trigger a reset. -/
def epochClockStep (q t : ℕ) (g : Bool) (z : EpochClock) : EpochClock :=
  if g then
    if z.gradients+1 = q then ⟨z.number+1,0,t+1⟩
    else {z with gradients := z.gradients+1}
  else z

def epochClock (q : ℕ) (g : ℕ → Bool) : ℕ → EpochClock
  | 0 => ⟨0,0,0⟩
  | t+1 => epochClockStep q t (g t) (epochClock q g t)

def epochOfStep (q : ℕ) (g : ℕ → Bool) (t : ℕ) : ℕ := gradientCount g t/q

theorem gradientCount_le (g : ℕ → Bool) (t : ℕ) : gradientCount g t ≤ t := by
  induction t with
  | zero => rfl
  | succ t ih => cases hg : g t <;> simp [gradientCount,hg] <;> omega

theorem gradientCount_mono (g : ℕ → Bool) : Monotone (gradientCount g) := by
  apply monotone_nat_of_le_succ
  intro t
  simp only [gradientCount]
  omega

theorem gradientCount_strict {g : ℕ → Bool} {i j : ℕ} (hij : i < j) (hg : g i = true) :
    gradientCount g i < gradientCount g j := by
  have hh := gradientCount_mono g (show i+1 ≤ j by omega)
  simp only [gradientCount,hg,↓reduceIte] at hh
  omega

theorem gradientCount_eq_sum (g : ℕ → Bool) (t : ℕ) :
    gradientCount g t = ∑ i ∈ Finset.range t, if g i then 1 else 0 := by
  induction t with
  | zero => simp [gradientCount]
  | succ t ih => rw [gradientCount, Finset.sum_range_succ, ih]

theorem epochClock_invariant {q : ℕ} (hq : 0 < q) (g : ℕ → Bool) (t : ℕ) :
    (epochClock q g t).gradients < q ∧
    gradientCount g t = (epochClock q g t).number*q+(epochClock q g t).gradients ∧
    (epochClock q g t).start ≤ t := by
  induction t with
  | zero => simpa [epochClock,gradientCount] using hq
  | succ t ih =>
    rcases ih with ⟨hr,hc,hs⟩
    cases hg : g t
    · simpa [epochClock,epochClockStep,gradientCount,hg] using ⟨hr,hc,hs.trans (Nat.le_succ t)⟩
    · by_cases he : (epochClock q g t).gradients+1 = q
      · simp only [epochClock,epochClockStep,hg,↓reduceIte,he,gradientCount,Nat.add_mul,Nat.one_mul]
        omega
      · simp only [epochClock,epochClockStep,hg,↓reduceIte,he,gradientCount]
        omega

theorem epochClock_number {q : ℕ} (hq : 0 < q) (g : ℕ → Bool) (t : ℕ) :
    (epochClock q g t).number = epochOfStep q g t := by
  obtain ⟨hr,hc,_⟩ := epochClock_invariant hq g t
  symm
  apply (Nat.div_eq_iff hq).mpr
  omega

theorem epochClock_gradients {q : ℕ} (hq : 0 < q) (g : ℕ → Bool) (t : ℕ) :
    (epochClock q g t).gradients = gradientCount g t%q := by
  obtain ⟨hr,hc,_⟩ := epochClock_invariant hq g t
  have hn := epochClock_number hq g t
  have hd := Nat.mod_add_div (gradientCount g t) q
  dsimp [epochOfStep] at hn
  rw [← hn, Nat.mul_comm q] at hd
  omega

theorem epochOfStep_mono (q : ℕ) (g : ℕ → Bool) : Monotone (epochOfStep q g) :=
  fun _ _ hij => Nat.div_le_div_right (gradientCount_mono g hij)

theorem epochOfStep_le (q : ℕ) (g : ℕ → Bool) (t : ℕ) : epochOfStep q g t ≤ t :=
  (Nat.div_le_self _ _).trans (gradientCount_le g t)

theorem epochClock_congr {q t : ℕ} {g h : ℕ → Bool} (hh : ∀ i < t, g i = h i) :
    epochClock q g t = epochClock q h t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [epochClock,epochClock,ih (fun i hi => hh i (by omega)), hh t (by omega)]

theorem gradientCount_congr {t : ℕ} {g h : ℕ → Bool} (hh : ∀ i < t, g i = h i) :
    gradientCount g t = gradientCount h t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [gradientCount,gradientCount,ih (fun i hi => hh i (by omega)), hh t (by omega)]

/-- The pre-move epoch label is determined by the previous move types. -/
theorem epochOfStep_congr {q t : ℕ} {g h : ℕ → Bool} (hh : ∀ i < t, g i = h i) :
    epochOfStep q g t = epochOfStep q h t := by
  unfold epochOfStep
  rw [gradientCount_congr hh]

theorem epochClock_start_same_epoch {q : ℕ} (hq : 0 < q) (g : ℕ → Bool) (t : ℕ) :
    ∀ k, (epochClock q g t).start ≤ k → k ≤ t → epochOfStep q g k = epochOfStep q g t := by
  induction t with
  | zero =>
    intro k hk ht
    have : k = 0 := by omega
    subst k
    rfl
  | succ t ih =>
    intro k hk ht
    by_cases hg : g t = true
    · by_cases he : (epochClock q g t).gradients+1 = q
      · have hs : (epochClock q g (t+1)).start = t+1 := by simp [epochClock,epochClockStep,hg,he]
        rw [hs] at hk
        have : k = t+1 := by omega
        subst k
        rfl
      · have hz : (epochClock q g (t+1)).number = (epochClock q g t).number := by
          simp [epochClock,epochClockStep,hg,he]
        have hs : (epochClock q g (t+1)).start = (epochClock q g t).start := by
          simp [epochClock,epochClockStep,hg,he]
        rw [hs] at hk
        by_cases hkt : k ≤ t
        · exact (ih k hk hkt).trans (by simpa only [epochClock_number hq] using hz.symm)
        · have : k = t+1 := by omega
          subst k
          rfl
    · have hz : epochClock q g (t+1) = epochClock q g t := by simp [epochClock,epochClockStep,hg]
      rw [hz] at hk
      by_cases hkt : k ≤ t
      · exact (ih k hk hkt).trans (by simpa only [epochClock_number hq] using congrArg EpochClock.number hz.symm)
      · have : k = t+1 := by omega
        subst k
        rfl

theorem epochClock_before_start {q : ℕ} (hq : 0 < q) (g : ℕ → Bool) (t : ℕ) :
    ∀ k < (epochClock q g t).start, epochOfStep q g k < epochOfStep q g t := by
  induction t with
  | zero => intro k hk; simp [epochClock] at hk
  | succ t ih =>
    intro k hk
    by_cases hg : g t = true
    · by_cases he : (epochClock q g t).gradients+1 = q
      · have hs : (epochClock q g (t+1)).start = t+1 := by simp [epochClock,epochClockStep,hg,he]
        have hn : epochOfStep q g (t+1) = epochOfStep q g t+1 := by
          rw [← epochClock_number hq,← epochClock_number hq]
          simp [epochClock,epochClockStep,hg,he]
        rw [hs] at hk
        rw [hn]
        exact (epochOfStep_mono q g (show k ≤ t by omega)).trans_lt (Nat.lt_succ_self _)
      · have hs : (epochClock q g (t+1)).start = (epochClock q g t).start := by
          simp [epochClock,epochClockStep,hg,he]
        have hn : epochOfStep q g (t+1) = epochOfStep q g t := by
          rw [← epochClock_number hq,← epochClock_number hq]
          simp [epochClock,epochClockStep,hg,he]
        rw [hn]
        exact ih k (hs ▸ hk)
    · have hz : epochClock q g (t+1) = epochClock q g t := by simp [epochClock,epochClockStep,hg]
      have hn : epochOfStep q g (t+1) = epochOfStep q g t := by
        simpa only [epochClock_number hq] using congrArg EpochClock.number hz
      rw [hn]
      exact ih k (hz ▸ hk)

theorem epochClock_interval {q : ℕ} (hq : 0 < q) (g : ℕ → Bool) {k t : ℕ} (hkt : k ≤ t) :
    epochOfStep q g k = epochOfStep q g t ↔ (epochClock q g t).start ≤ k := by
  constructor
  · intro he
    by_contra hh
    have hh' := epochClock_before_start hq g t k (Nat.lt_of_not_ge hh)
    omega
  · exact fun hh => epochClock_start_same_epoch hq g t k hh hkt

theorem epochClock_start_constant {q : ℕ} (hq : 0 < q) (g : ℕ → Bool) {i j : ℕ}
    (he : epochOfStep q g i = epochOfStep q g j) :
    (epochClock q g i).start = (epochClock q g j).start := by
  suffices ∀ i j, i ≤ j → epochOfStep q g i = epochOfStep q g j →
      (epochClock q g i).start = (epochClock q g j).start by
    rcases le_total i j with hij | hji
    · exact this i j hij he
    · exact (this j i hji he.symm).symm
  intro i j hij he
  have hi := (epochClock_invariant hq g i).2.2
  have hj := (epochClock_invariant hq g j).2.2
  have hei := epochClock_start_same_epoch hq g i _ (Nat.le_refl _) hi
  have hej := epochClock_start_same_epoch hq g j _ (Nat.le_refl _) hj
  have hji := (epochClock_interval hq g (hi.trans hij)).mp (hei.trans he)
  have hij' := (epochClock_interval hq g (hji.trans hi)).mp (hej.trans he.symm)
  omega

/-- Epoch number and local physical offset together identify a move.
This is the address used when a binary tree is restarted at each epoch. -/
def epochAddress (q : ℕ) (g : ℕ → Bool) (t : ℕ) : ℕ × ℕ :=
  (epochOfStep q g t,t-(epochClock q g t).start)

theorem epochAddress_injective {q : ℕ} (hq : 0 < q) (g : ℕ → Bool) :
    Function.Injective (epochAddress q g) := by
  intro i j hij
  have he : epochOfStep q g i = epochOfStep q g j := congrArg Prod.fst hij
  have hl : i-(epochClock q g i).start = j-(epochClock q g j).start := congrArg Prod.snd hij
  have hs := epochClock_start_constant hq g he
  have hi := (epochClock_invariant hq g i).2.2
  have hj := (epochClock_invariant hq g j).2.2
  omega

end SecondOrder
