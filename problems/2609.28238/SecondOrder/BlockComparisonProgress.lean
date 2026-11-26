import SecondOrder.BlockActivationIndex

open MeasureTheory ProbabilityTheory
open scoped Classical

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u}

/-- Historical progress computed from an arbitrary actual reply history.
The query maps cannot inspect hidden parameters except through replies. -/
def blockComparisonProgress (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) :
    (n : ℕ) → FiniteHistory S A n → ℕ
  | 0, _ => 0
  | n+1, h => max (blockComparisonProgress active query Θ n h.1)
      (blockActivationIndex active Θ (query n h.1) (blockComparisonProgress active query Θ n h.1+1))

def blockComparisonIndex (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H)
    (n : ℕ) (h : FiniteHistory S A n) : ℕ :=
  blockActivationIndex active Θ (query n h) (blockComparisonProgress active query Θ n h+1)

theorem blockComparisonProgress_succ (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H)
    (n : ℕ) (h : FiniteHistory S A (n+1)) :
    blockComparisonProgress active query Θ (n+1) h = max
      (blockComparisonProgress active query Θ n h.1) (blockComparisonIndex active query Θ n h.1) := rfl

theorem blockComparisonProgress_le (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) :
    ∀ n h, blockComparisonProgress active query Θ n h≤T := by
  intro n
  induction n with
  | zero => intro h; exact Nat.zero_le _
  | succ n ih => intro h; exact max_le (ih h.1) (blockActivationIndex_le active Θ _ _).1

theorem blockComparisonIndex_le (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H)
    (n : ℕ) (h : FiniteHistory S A n) :
    blockComparisonIndex active query Θ n h≤T ∧
      blockComparisonIndex active query Θ n h≤blockComparisonProgress active query Θ n h+1 :=
  blockActivationIndex_le active Θ _ _

theorem blockComparisonProgress_step (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H)
    (n : ℕ) (h : FiniteHistory S A (n+1)) :
    blockComparisonProgress active query Θ n h.1≤blockComparisonProgress active query Θ (n+1) h ∧
      blockComparisonProgress active query Θ (n+1) h≤blockComparisonProgress active query Θ n h.1+1 :=
  ⟨le_max_left _ _,max_le (Nat.le_succ _) (blockComparisonIndex_le active query Θ n h.1).2⟩

/-- Even on a supplied reply history, progress inspects no hidden block
beyond the first block after its final historical progress. -/
theorem blockComparisonProgress_prefix (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ Θ' : Fin T → H) :
    ∀ n h, (∀ i, i.val<blockComparisonProgress active query Θ n h+1 → Θ i=Θ' i) →
      blockComparisonProgress active query Θ n h=blockComparisonProgress active query Θ' n h := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro h hΘ
    have hp := (blockComparisonProgress_step active query Θ n h).1
    have hprev : ∀ i, i.val<blockComparisonProgress active query Θ n h.1+1 → Θ i=Θ' i :=
      fun i hi => hΘ i (by omega)
    have he := ih h.1 hprev
    simp only [blockComparisonProgress,←he]
    rw [blockActivationIndex_prefix active Θ Θ' _ _ hprev]

theorem blockComparisonIndex_prefix (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ Θ' : Fin T → H)
    (n : ℕ) (h : FiniteHistory S A n)
    (hΘ : ∀ i, i.val<blockComparisonProgress active query Θ n h+1 → Θ i=Θ' i) :
    blockComparisonIndex active query Θ n h=blockComparisonIndex active query Θ' n h := by
  unfold blockComparisonIndex
  rw [←blockComparisonProgress_prefix active query Θ Θ' n h hΘ]
  exact blockActivationIndex_prefix active Θ Θ' _ _ hΘ

theorem blockComparisonProgress_measurable [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace S] [MeasurableSpace A]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n)) :
    ∀ n, Measurable (fun z : (Fin T → H) × FiniteHistory S A n =>
      blockComparisonProgress active query z.1 n z.2) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hp : Measurable (fun z : (Fin T → H) × FiniteHistory S A (n+1) =>
        blockComparisonProgress active query z.1 n z.2.1) :=
      ih.comp (measurable_fst.prodMk measurable_snd.fst)
    change Measurable (fun z : (Fin T → H) × (FiniteHistory S A n × A) =>
      max (blockComparisonProgress active query z.1 n z.2.1)
        (blockActivationIndex active z.1 (query n z.2.1) (blockComparisonProgress active query z.1 n z.2.1+1)))
    exact hp.max (blockActivationIndex_measurable active ha
      (B := (Fin T → H) × (FiniteHistory S A n × A)) (fun z => z.1)
      (fun z => query n z.2.1) (fun z => blockComparisonProgress active query z.1 n z.2.1+1)
      (fun i => (measurable_pi_apply i).comp measurable_fst) ((hq n).comp measurable_snd.fst)
      (hp.add_const 1))

theorem blockComparisonIndex_measurable [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace S] [MeasurableSpace A]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n)) (n : ℕ) :
    Measurable (fun z : (Fin T → H) × FiniteHistory S A n => blockComparisonIndex active query z.1 n z.2) :=
  blockActivationIndex_measurable active ha (B := (Fin T → H) × FiniteHistory S A n)
    (fun z => z.1) (fun z => query n z.2)
    (fun z => blockComparisonProgress active query z.1 n z.2+1)
    (fun i => (measurable_pi_apply i).comp measurable_fst) ((hq n).comp measurable_snd)
    ((blockComparisonProgress_measurable active ha query hq n).add_const 1)

end
end SecondOrder
