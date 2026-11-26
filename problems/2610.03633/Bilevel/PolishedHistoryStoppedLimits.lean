import Bilevel.PolishedHistoryAbsorption

/-! Deterministic stopping identities used to compare actual execution
measures. Nontermination is retained with infinite original-call cost. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open HistoryProgram
set_option autoImplicit false
variable {S Q O Y H : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y] [MeasurableSpace H]
variable (A : BorelAdaptive.Program S Q O Y)

def HaltSticky (w : HistoryProgram.Path S H) : Prop :=
  ∀ n,A.halt (w n).1=true → A.halt (w (n+1)).1=true

omit [MeasurableSpace H] in
theorem sticky_halt_after (w : HistoryProgram.Path S H) (hw : HaltSticky A w)
    (m : ℕ) (hm : A.halt (w m).1=true) (k : ℕ) : A.halt (w (m+k)).1=true := by
  induction k with
  | zero => simpa only [Nat.add_zero] using hm
  | succ k ih => exact hw (m+k) ih

def queryCount : ℕ → HistoryProgram.Path S H → ℕ
  | 0,_ => 0
  | n+1,w => queryCount n w+if A.halt (w n).1=true then 0 else 1

theorem queryCount_measurable (n : ℕ) : Measurable (queryCount A (H:=H) n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hh : MeasurableSet {w : HistoryProgram.Path S H | A.halt (w n).1=true} :=
        (A.halt_measurable.comp (measurable_fst.comp (measurable_pi_apply n)))
          (measurableSet_singleton true)
      exact ih.add (measurable_const.ite hh measurable_const)

omit [MeasurableSpace H] in
theorem queryCount_mono (w : HistoryProgram.Path S H) : Monotone (fun n => queryCount A n w) :=
  monotone_nat_of_le_succ (fun _ => Nat.le_add_right _ _)

omit [MeasurableSpace H] in
theorem sticky_halt_iff (w : HistoryProgram.Path S H) (hw : HaltSticky A w)
    (ht : HistoryProgram.Terminated A w) (n : ℕ) :
    A.halt (w n).1=true ↔ HistoryProgram.stopTime A w≤n := by
  constructor
  · intro hn
    simpa only [HistoryProgram.stopTime,dif_pos ht] using Nat.find_min' ht hn
  · intro hn
    have h := sticky_halt_after A w hw (HistoryProgram.stopTime A w)
      (HistoryProgram.stopTime_halted A w ht) (n-HistoryProgram.stopTime A w)
    simpa only [Nat.add_sub_of_le hn] using h

omit [MeasurableSpace H] in
theorem queryCount_eq_min (w : HistoryProgram.Path S H) (hw : HaltSticky A w)
    (ht : HistoryProgram.Terminated A w) (n : ℕ) :
    queryCount A n w=min n (HistoryProgram.stopTime A w) := by
  induction n with
  | zero => simp [queryCount]
  | succ n ih =>
      by_cases hn : n<HistoryProgram.stopTime A w
      · have hh : ¬A.halt (w n).1=true := by
          rw [sticky_halt_iff A w hw ht]
          exact Nat.not_le.mpr hn
        simp only [queryCount,ih,if_neg hh,Nat.min_eq_left hn.le,
          Nat.min_eq_left (Nat.succ_le_of_lt hn)]
      · have hn' : HistoryProgram.stopTime A w≤n := Nat.le_of_not_gt hn
        have hh := (sticky_halt_iff A w hw ht n).mpr hn'
        simp only [queryCount,ih,if_pos hh,Nat.add_zero,Nat.min_eq_right hn',
          Nat.min_eq_right (hn'.trans (Nat.le_succ n))]

omit [MeasurableSpace H] in
/-- The path's actual extended stopping count is the increasing supremum
of original live-call counts, including an infinite nonterminating path. -/
theorem totalCalls_eq_iSup_queryCount (w : HistoryProgram.Path S H)
    (hw : HaltSticky A w) :
    HistoryProgram.totalCalls A w=⨆ n : ℕ,(queryCount A n w:ℝ≥0∞) := by
  classical
  by_cases ht : HistoryProgram.Terminated A w
  · rw [HistoryProgram.totalCalls,if_pos ht]
    apply le_antisymm
    · exact le_iSup_of_le (HistoryProgram.stopTime A w)
        (by rw [queryCount_eq_min A w hw ht]; simp)
    · apply iSup_le
      intro n
      rw [queryCount_eq_min A w hw ht]
      exact Nat.cast_le.mpr (Nat.min_le_right _ _)
  · have hcount (n : ℕ) : queryCount A n w=n := by
      induction n with
      | zero => rfl
      | succ n ih =>
          have hh : ¬A.halt (w n).1=true := fun h => ht ⟨n,h⟩
          simp only [queryCount,ih,if_neg hh]
    simp only [HistoryProgram.totalCalls,if_neg ht,hcount,ENNReal.iSup_natCast]

def revealedLoss (v : S → ℝ) (n : ℕ) (w : HistoryProgram.Path S H) : ℝ≥0∞ :=
  if A.halt (w n).1=true then ENNReal.ofReal (v (w n).1) else 0

theorem revealedLoss_measurable (v : S → ℝ) (hv : Measurable v) (n : ℕ) :
    Measurable (revealedLoss A (H:=H) v n) := by
  have hs : Measurable (fun w : HistoryProgram.Path S H => (w n).1) :=
    measurable_fst.comp (measurable_pi_apply n)
  exact ((hv.comp hs).ennreal_ofReal).ite
    ((A.halt_measurable.comp hs) (measurableSet_singleton true)) measurable_const

omit [MeasurableSpace H] in
theorem observable_after (v : S → ℝ) (w : HistoryProgram.Path S H)
    (hw : ∀ n,pathStepGood A v n w) (m : ℕ) (hm : A.halt (w m).1=true) (k : ℕ) :
    A.halt (w (m+k)).1=true ∧ v (w (m+k)).1=v (w m).1 := by
  induction k with
  | zero => exact ⟨hm,rfl⟩
  | succ k ih =>
      have hh := hw (m+k) ih.1
      exact ⟨hh.1,hh.2.trans ih.2⟩

omit [MeasurableSpace H] in
theorem revealedLoss_mono (v : S → ℝ) (w : HistoryProgram.Path S H)
    (hw : ∀ n,pathStepGood A v n w) : Monotone (fun n => revealedLoss A v n w) := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hh : A.halt (w n).1=true
  · have hn := hw n hh
    simp only [revealedLoss,if_pos hh,if_pos hn.1,hn.2,le_refl]
  · simp only [revealedLoss,if_neg hh]
    exact zero_le _

omit [MeasurableSpace H] in
/-- Along any terminated absorbing path, the revealed losses increase to
the actual stopped loss. The theorem makes no integrability assumption. -/
theorem iSup_revealedLoss (v : S → ℝ) (w : HistoryProgram.Path S H)
    (hw : ∀ n,pathStepGood A v n w) (ht : HistoryProgram.Terminated A w) :
    (⨆ n : ℕ,revealedLoss A v n w)=
      ENNReal.ofReal (v (w (HistoryProgram.stopTime A w)).1) := by
  have hsticky : HaltSticky A w := fun n hh => (hw n hh).1
  apply le_antisymm
  · apply iSup_le
    intro n
    by_cases hh : A.halt (w n).1=true
    · have hn := (sticky_halt_iff A w hsticky ht n).mp hh
      have ho := observable_after A v w hw (HistoryProgram.stopTime A w)
        (HistoryProgram.stopTime_halted A w ht) (n-HistoryProgram.stopTime A w)
      rw [Nat.add_sub_of_le hn] at ho
      simp only [revealedLoss,if_pos hh,ho.2,le_refl]
    · simp only [revealedLoss,if_neg hh]
      exact zero_le _
  · exact le_iSup_of_le (HistoryProgram.stopTime A w)
      (by rw [revealedLoss,if_pos (HistoryProgram.stopTime_halted A w ht)])

end Bilevel.PolishedHistory
