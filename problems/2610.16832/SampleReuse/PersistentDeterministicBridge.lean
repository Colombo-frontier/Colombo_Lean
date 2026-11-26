import SampleReuse.PersistentStopping
import SampleReuse.RandomFrameExtendedCost

open SecondOrder MeasureTheory
open scoped Classical ENNReal
namespace SampleReuse
noncomputable section

structure MeasurableStoppingFamily {Q H Y O S Ξ : Type*}
    [MeasurableSpace Q] [MeasurableSpace Y] [MeasurableSpace O]
    [MeasurableSpace S] [MeasurableSpace Ξ]
    (P : Ξ → PersistentStoppingAlgorithm Q H Y O S) : Prop where
  initial : Measurable (fun ξ => (P ξ).initial)
  queryPoint : ∀ n, Measurable (fun w : Ξ × S => ((P w.1).query n w.2).1)
  update : ∀ n, Measurable (fun w : Ξ × (S × Y) => (P w.1).update n w.2.1 w.2.2)
  stop : ∀ n, Measurable (fun w : Ξ × S => (P w.1).stop n w.2)
  output : ∀ n, Measurable (fun w : Ξ × S => (P w.1).output n w.2)

def replyHistoryState {Q H Y O S Ξ : Type*} (P : Ξ → PersistentStoppingAlgorithm Q H Y O S) :
    (n : ℕ) → Ξ → (Fin n → Y) → S
  | 0,ξ,_ => (P ξ).initial
  | n+1,ξ,z => (P ξ).update n (replyHistoryState P n ξ (fun i => z i.castSucc)) (z (Fin.last n))

theorem measurable_replyHistoryState {Q H Y O S Ξ : Type*}
    [MeasurableSpace Q] [MeasurableSpace Y] [MeasurableSpace O]
    [MeasurableSpace S] [MeasurableSpace Ξ]
    (P : Ξ → PersistentStoppingAlgorithm Q H Y O S) (hP : MeasurableStoppingFamily P) (n : ℕ) :
    Measurable (fun w : Ξ × (Fin n → Y) => replyHistoryState P n w.1 w.2) := by
  induction n with
  | zero => exact hP.initial.comp measurable_fst
  | succ n ih =>
    have hp : Measurable (fun w : Ξ × (Fin (n+1) → Y) =>
        replyHistoryState P n w.1 (fun i => w.2 i.castSucc)) :=
      ih.comp (measurable_fst.prodMk (measurable_pi_lambda _
        (fun i => (measurable_pi_apply i.castSucc).comp measurable_snd)))
    exact (hP.update n).comp (measurable_fst.prodMk
      (hp.prodMk ((measurable_pi_apply (Fin.last n)).comp measurable_snd)))

def deterministicFullJetPolicy {d : ℕ} {H S Ξ : Type*}
    [MeasurableSpace S] [MeasurableSpace Ξ]
    (P : Ξ → PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (hP : MeasurableStoppingFamily P) : RandomFrame.StoppingFullJetPolicy d Ξ where
  query n ξ z := ((P ξ).query n (replyHistoryState P n ξ z)).1
  query_measurable n := (hP.queryPoint n).comp
    (measurable_fst.prodMk (measurable_replyHistoryState P hP n))
  stop n ξ z := (P ξ).stop n (replyHistoryState P n ξ z)
  stop_measurable n := (hP.stop n).comp
    (measurable_fst.prodMk (measurable_replyHistoryState P hP n))
  output n ξ z := (P ξ).output n (replyHistoryState P n ξ z)
  output_measurable n := (hP.output n).comp
    (measurable_fst.prodMk (measurable_replyHistoryState P hP n))

theorem replyHistoryState_unit_run {d : ℕ} {H S Ξ : Type*}
    [MeasurableSpace S] [MeasurableSpace Ξ]
    (P : Ξ → PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (hP : MeasurableStoppingFamily P) (f : Point d → ℝ) (ξ : Ξ) (tape : ℕ → Unit) : ∀ n,
    replyHistoryState P n ξ (RandomFrame.responseHistory (deterministicFullJetPolicy P hP).query
      (fun _ (_ : Unit) => RandomFrame.fullJet f) ξ () n) =
      (P ξ).state (fun x (_ : Unit) => RandomFrame.fullJet f x) tape n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [replyHistoryState,RandomFrame.responseHistory,Fin.snoc_castSucc,Fin.snoc_last]
    change (P ξ).update n
      (replyHistoryState P n ξ (RandomFrame.responseHistory (deterministicFullJetPolicy P hP).query
        (fun _ (_ : Unit) => RandomFrame.fullJet f) ξ () n))
      (RandomFrame.fullJet f (((P ξ).query n
        (replyHistoryState P n ξ (RandomFrame.responseHistory (deterministicFullJetPolicy P hP).query
          (fun _ (_ : Unit) => RandomFrame.fullJet f) ξ () n))).1)) = _
    rw [ih]
    rfl

theorem deterministicBridge_stop {d : ℕ} {H S Ξ : Type*}
    [MeasurableSpace S] [MeasurableSpace Ξ]
    (P : Ξ → PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (hP : MeasurableStoppingFamily P) (f : Point d → ℝ) (ξ : Ξ) (tape : ℕ → Unit) (n : ℕ) :
    (deterministicFullJetPolicy P hP).stop n ξ
      (RandomFrame.responseHistory (deterministicFullJetPolicy P hP).query
        (fun _ (_ : Unit) => RandomFrame.fullJet f) ξ () n) =
      (P ξ).stopOnRun (fun x (_ : Unit) => RandomFrame.fullJet f x) tape n := by
  change (P ξ).stop n _ = _
  rw [replyHistoryState_unit_run P hP f ξ tape n]
  rfl

theorem deterministicBridge_halts {d : ℕ} {H S Ξ : Type*}
    [MeasurableSpace S] [MeasurableSpace Ξ]
    (P : Ξ → PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (hP : MeasurableStoppingFamily P) (f : Point d → ℝ) (ξ : Ξ) (tape : ℕ → Unit) :
    (deterministicFullJetPolicy P hP).Halts f ξ ↔
      (P ξ).Halts (fun x (_ : Unit) => RandomFrame.fullJet f x) tape := by
  simp only [RandomFrame.StoppingFullJetPolicy.Halts,PersistentStoppingAlgorithm.Halts,
    deterministicBridge_stop P hP f ξ tape]

theorem deterministicBridge_cost {d : ℕ} {H S Ξ : Type*}
    [MeasurableSpace S] [MeasurableSpace Ξ]
    (P : Ξ → PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (hP : MeasurableStoppingFamily P) (f : Point d → ℝ) (ξ : Ξ) (tape : ℕ → Unit) :
    (deterministicFullJetPolicy P hP).cost f ξ =
      (P ξ).cost (fun x (_ : Unit) => RandomFrame.fullJet f x) tape := by
  unfold RandomFrame.StoppingFullJetPolicy.cost PersistentStoppingAlgorithm.cost
  simp only [RandomFrame.StoppingFullJetPolicy.Halts,PersistentStoppingAlgorithm.Halts,
    deterministicBridge_stop P hP f ξ tape]

theorem deterministicBridge_output {d : ℕ} {H S Ξ : Type*}
    [MeasurableSpace S] [MeasurableSpace Ξ]
    (P : Ξ → PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (hP : MeasurableStoppingFamily P) (f : Point d → ℝ) (ξ : Ξ) (tape : ℕ → Unit) :
    (deterministicFullJetPolicy P hP).outputFor f ξ =
      (P ξ).outputFor (fun x (_ : Unit) => RandomFrame.fullJet f x) tape := by
  unfold RandomFrame.StoppingFullJetPolicy.outputFor
  change (P ξ).output _ (replyHistoryState P _ ξ _) = _
  rw [replyHistoryState_unit_run P hP f ξ tape,deterministicBridge_cost P hP f ξ tape]
  rfl

theorem deterministicBridge_extendedCost {d : ℕ} {H S Ξ : Type*}
    [MeasurableSpace S] [MeasurableSpace Ξ]
    (P : Ξ → PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (hP : MeasurableStoppingFamily P) (f : Point d → ℝ) (ξ : Ξ) (tape : ℕ → Unit) :
    (deterministicFullJetPolicy P hP).extendedCost f ξ =
      (P ξ).extendedCost (fun x (_ : Unit) => RandomFrame.fullJet f x) tape := by
  simp only [RandomFrame.StoppingFullJetPolicy.extendedCost,PersistentStoppingAlgorithm.extendedCost,
    RandomFrame.StoppingFullJetPolicy.NoStopBefore,PersistentStoppingAlgorithm.NoStopBefore,
    deterministicBridge_stop P hP f ξ tape]
  apply iSup_congr
  intro n
  split_ifs <;> rfl

end
end SampleReuse
