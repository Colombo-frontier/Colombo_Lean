import Nonsmooth.SupportObservation

open MeasureTheory
open scoped InnerProductSpace
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {k : ℕ} [Nonempty (Fin k)] {Ω S : Type}

abbrev SupportHistory (E : Type) (k n : ℕ) := Fin n → E × (Fin k × ℝ)

def supportEraseHistory {n : ℕ} (h : SupportHistory E k n) : History E n :=
  fun j => ((h j).1, (h j).2.2)

theorem supportEraseHistory_snoc {n : ℕ} (h : SupportHistory E k n) (v : E × (Fin k × ℝ)) :
    supportEraseHistory (Fin.snoc h v) = Fin.snoc (supportEraseHistory h) (v.1, v.2.2) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [supportEraseHistory]

/-- The actual policy receives only the erased scalar-value history. Winner indices
are added to the record after the query and do not alter the policy's state. -/
def supportAugmentedTranscript (p : Policy Ω S E) (a : Fin k → E) (ω : Ω) :
    (n : ℕ) → SupportHistory E k n
  | 0 => Fin.elim0
  | n + 1 =>
    let h := supportAugmentedTranscript p a ω n
    let x := p.query n ω (p.stateOnHistory ω n (supportEraseHistory h))
    Fin.snoc h (x, (supportWinner a x, finiteSupport a x))

theorem supportAugmentedTranscript_erases (p : Policy Ω S E) (a : Fin k → E) (ω : Ω) (n : ℕ) :
    supportEraseHistory (supportAugmentedTranscript p a ω n) = p.toHistory.transcript (finiteSupport a) ω n := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    simp only [supportAugmentedTranscript, supportEraseHistory_snoc, ih,
      HistoryPolicy.transcript, Policy.toHistory]

theorem supportAugmentedTranscript_state (p : Policy Ω S E) (a : Fin k → E) (ω : Ω) (n : ℕ) :
    p.stateOnHistory ω n (supportEraseHistory (supportAugmentedTranscript p a ω n)) =
      p.run (finiteSupport a) ω n := by
  rw [supportAugmentedTranscript_erases, state_toHistory_run]

theorem supportAugmentedTranscript_output (p : Policy Ω S E) (a : Fin k → E) (ω : Ω) (n : ℕ) :
    p.output ω (p.stateOnHistory ω n (supportEraseHistory (supportAugmentedTranscript p a ω n))) =
      p.result (finiteSupport a) ω n := by
  rw [supportAugmentedTranscript_state]
  rfl

def supportHistoryConsistent (p : Policy Ω S E) (ω : Ω) : (n : ℕ) → SupportHistory E k n → Prop
  | 0, _ => True
  | n + 1, h => supportHistoryConsistent p ω n (Fin.init h) ∧
      (h (Fin.last n)).1 = p.query n ω (p.stateOnHistory ω n (supportEraseHistory (Fin.init h)))

def supportHistoryCell : (n : ℕ) → SupportHistory E k n → Fin k → Set E
  | 0, _, _ => Set.univ
  | n + 1, h, i => supportHistoryCell n (Fin.init h) i ∩
      supportObservationCell i (h (Fin.last n)).2.1 (h (Fin.last n)).1 (h (Fin.last n)).2.2

/-- Exact fibers, including impossible histories and deterministic ties. This is a
geometric identity; it does not identify a conditional probability on a null fiber. -/
theorem supportAugmentedTranscript_fiber (p : Policy Ω S E) (a : Fin k → E) (ω : Ω)
    (n : ℕ) (h : SupportHistory E k n) :
    supportAugmentedTranscript p a ω n = h ↔
      supportHistoryConsistent p ω n h ∧ ∀ i, a i ∈ supportHistoryCell n h i := by
  induction n with
  | zero => simp only [supportHistoryConsistent, supportHistoryCell, Set.mem_univ, implies_true, and_self]
            exact iff_of_true (Subsingleton.elim _ _) trivial
  | succ n ih =>
    constructor
    · intro he
      have hp : supportAugmentedTranscript p a ω n = Fin.init h := by
        simpa only [supportAugmentedTranscript, Fin.init_snoc] using congrArg Fin.init he
      have hl := congr_fun he (Fin.last n)
      simp only [supportAugmentedTranscript, Fin.snoc_last, hp] at hl
      have hq := (congrArg Prod.fst hl).symm
      have hw := congrArg (fun v : E × (Fin k × ℝ) => v.2.1) hl
      have hy := congrArg (fun v : E × (Fin k × ℝ) => v.2.2) hl
      dsimp only at hq hw hy
      have hc := (support_observation_fiber a (h (Fin.last n)).1 (h (Fin.last n)).2.1
        (h (Fin.last n)).2.2).mp ⟨by rwa [← hq] at hw, by rwa [← hq] at hy⟩
      have hprev := (ih (Fin.init h)).mp hp
      exact ⟨⟨hprev.1, hq⟩, fun i => ⟨hprev.2 i, hc i⟩⟩
    · rintro ⟨⟨hprev, hq⟩, hc⟩
      have hp : supportAugmentedTranscript p a ω n = Fin.init h :=
        (ih (Fin.init h)).mpr ⟨hprev, fun i => (hc i).1⟩
      have ho := (support_observation_fiber a (h (Fin.last n)).1 (h (Fin.last n)).2.1
        (h (Fin.last n)).2.2).mpr (fun i => (hc i).2)
      simp only [supportAugmentedTranscript, hp]
      rw [← hq, ho.1, ho.2]
      exact Fin.snoc_init_self h

theorem supportHistoryCell_convex (n : ℕ) (h : SupportHistory E k n) (i : Fin k) :
    Convex ℝ (supportHistoryCell n h i) := by
  induction n with
  | zero => exact convex_univ
  | succ n ih => exact (ih (Fin.init h)).inter (supportObservationCell_convex _ _ _ _)

theorem supportHistoryCell_winner_equalities (n : ℕ) (h : SupportHistory E k n)
    (i : Fin k) (b : E) (hb : b ∈ supportHistoryCell n h i) :
    ∀ j : Fin n, i = (h j).2.1 → ⟪b, (h j).1⟫_ℝ = (h j).2.2 := by
  induction n with
  | zero => intro j; exact Fin.elim0 j
  | succ n ih =>
    intro j
    refine Fin.lastCases ?_ (fun t => ?_) j
    · exact hb.2.2.1
    · exact ih (Fin.init h) hb.1 t

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] [MeasurableSpace S]

theorem supportEraseHistory_measurable (n : ℕ) :
    Measurable (supportEraseHistory (E := E) (k := k) (n := n)) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_fst.comp (measurable_pi_apply i)).prodMk
    (measurable_snd.comp (measurable_snd.comp (measurable_pi_apply i)))

theorem supportAugmentedTranscript_measurable (p : Policy Ω S E) (hp : p.IsMeasurable) (n : ℕ) :
    Measurable (fun z : (Fin k → E) × Ω => supportAugmentedTranscript p z.1 z.2 n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hs := (stateOnHistory_measurable hp n).comp
      (measurable_snd.prodMk ((supportEraseHistory_measurable n).comp ih))
    have hx := (hp.query n).comp (measurable_snd.prodMk hs)
    have hw := supportWinner_measurable.comp (measurable_fst.prodMk hx)
    have hy := finiteSupport_joint_continuous.measurable.comp (measurable_fst.prodMk hx)
    apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · convert! hx.prodMk (hw.prodMk hy) using 1 <;>
        simp only [supportAugmentedTranscript, Fin.snoc_last, Function.comp_def]
    · convert! (measurable_pi_apply j).comp ih using 1 <;>
        simp only [supportAugmentedTranscript, Fin.snoc_castSucc, Function.comp_def]

theorem supportHistoryCell_measurable (n : ℕ) (h : SupportHistory E k n) (i : Fin k) :
    MeasurableSet (supportHistoryCell n h i) := by
  induction n with
  | zero => exact MeasurableSet.univ
  | succ n ih => exact (ih (Fin.init h)).inter (supportObservationCell_measurable _ _ _ _)

end
end Nonsmooth

