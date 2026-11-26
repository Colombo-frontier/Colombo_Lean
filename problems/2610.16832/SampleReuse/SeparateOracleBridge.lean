import SampleReuse.PersistentLowerInterface
import SampleReuse.PersistentDeterministicBridge
import SampleReuse.OraclePersistent

open SecondOrder MeasureTheory
open scoped Classical ENNReal

namespace SampleReuse
noncomputable section

def richToSeparate {d : ℕ} (kind : Bool) (y : RichReply d) : PersistentReply d :=
  if kind then (y.2.1,0) else (0,y.2.2)

def separateSampleReply {Z : Type*} {d : ℕ} (F : Z → Point d → ℝ)
    (q : Bool × Point d) (z : Z) : PersistentReply d :=
  richToSeparate q.1 (richReply F z q.2)

/-- The stronger oracle simulates either source derivative request in one
call, discarding the value and the unrequested derivative. -/
def toFullJetStopping {H S : Type*} {d : ℕ}
    (P : PersistentStoppingAlgorithm (Bool × Point d) H (PersistentReply d) (Point d) S) :
    PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S where
  initial := P.initial
  query n s := ((P.query n s).1.2,(P.query n s).2)
  update n s y := P.update n s (richToSeparate (P.query n s).1.1 y)
  output := P.output
  stop := P.stop

theorem toFullJetStopping_measurable {H S Ξ : Type*} {d : ℕ}
    [MeasurableSpace S] [MeasurableSpace Ξ]
    (P : Ξ → PersistentStoppingAlgorithm (Bool × Point d) H (PersistentReply d) (Point d) S)
    (hP : MeasurableStoppingFamily P) :
    MeasurableStoppingFamily (fun ξ => toFullJetStopping (P ξ)) := by
  refine ⟨hP.initial,fun n => (hP.queryPoint n).snd,?_,hP.stop,hP.output⟩
  intro n
  have hk : Measurable (fun w : Ξ × (S × RichReply d) =>
      ((P w.1).query n w.2.1).1.1) :=
    (hP.queryPoint n).fst.comp (measurable_fst.prodMk measurable_snd.fst)
  have hr : Measurable (fun w : Ξ × (S × RichReply d) =>
      richToSeparate ((P w.1).query n w.2.1).1.1 w.2.2) := by
    unfold richToSeparate
    exact Measurable.ite (hk (measurableSet_singleton true))
      (measurable_snd.snd.snd.fst.prodMk measurable_const)
      (measurable_const.prodMk measurable_snd.snd.snd.snd)
  exact (hP.update n).comp (measurable_fst.prodMk (measurable_snd.fst.prodMk hr))

theorem toFullJetStopping_run {H S Z : Type*} {d : ℕ}
    (P : PersistentStoppingAlgorithm (Bool × Point d) H (PersistentReply d) (Point d) S)
    (F : Z → Point d → ℝ) (tape : ℕ → Z) : ∀ n,
    lazyPersistentRun (toFullJetStopping P).toQueryPolicy (fun x z => richReply F z x) tape n =
      lazyPersistentRun P.toQueryPolicy (separateSampleReply F) tape n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [lazyPersistentRun,lazyPersistentRun,ih]
    rfl

theorem toFullJetStopping_stopOnRun {H S Z : Type*} {d : ℕ}
    (P : PersistentStoppingAlgorithm (Bool × Point d) H (PersistentReply d) (Point d) S)
    (F : Z → Point d → ℝ) (tape : ℕ → Z) (n : ℕ) :
    (toFullJetStopping P).stopOnRun (fun x z => richReply F z x) tape n =
      P.stopOnRun (separateSampleReply F) tape n := by
  unfold PersistentStoppingAlgorithm.stopOnRun PersistentStoppingAlgorithm.state
  rw [toFullJetStopping_run]
  rfl

theorem toFullJetStopping_outputAt {H S Z : Type*} {d : ℕ}
    (P : PersistentStoppingAlgorithm (Bool × Point d) H (PersistentReply d) (Point d) S)
    (F : Z → Point d → ℝ) (tape : ℕ → Z) (n : ℕ) :
    (toFullJetStopping P).outputAt (fun x z => richReply F z x) tape n =
      P.outputAt (separateSampleReply F) tape n := by
  unfold PersistentStoppingAlgorithm.outputAt PersistentStoppingAlgorithm.state
  rw [toFullJetStopping_run]
  rfl

theorem toFullJetStopping_halts {H S Z : Type*} {d : ℕ}
    (P : PersistentStoppingAlgorithm (Bool × Point d) H (PersistentReply d) (Point d) S)
    (F : Z → Point d → ℝ) (tape : ℕ → Z) :
    (toFullJetStopping P).Halts (fun x z => richReply F z x) tape ↔
      P.Halts (separateSampleReply F) tape := by
  simp only [PersistentStoppingAlgorithm.Halts,toFullJetStopping_stopOnRun]

theorem toFullJetStopping_cost {H S Z : Type*} {d : ℕ}
    (P : PersistentStoppingAlgorithm (Bool × Point d) H (PersistentReply d) (Point d) S)
    (F : Z → Point d → ℝ) (tape : ℕ → Z) :
    (toFullJetStopping P).cost (fun x z => richReply F z x) tape =
      P.cost (separateSampleReply F) tape := by
  simp only [PersistentStoppingAlgorithm.cost,PersistentStoppingAlgorithm.Halts,
    toFullJetStopping_stopOnRun]

theorem toFullJetStopping_outputFor {H S Z : Type*} {d : ℕ}
    (P : PersistentStoppingAlgorithm (Bool × Point d) H (PersistentReply d) (Point d) S)
    (F : Z → Point d → ℝ) (tape : ℕ → Z) :
    (toFullJetStopping P).outputFor (fun x z => richReply F z x) tape =
      P.outputFor (separateSampleReply F) tape := by
  simp only [PersistentStoppingAlgorithm.outputFor,toFullJetStopping_cost,toFullJetStopping_outputAt]

theorem toFullJetStopping_extendedCost {H S Z : Type*} {d : ℕ}
    (P : PersistentStoppingAlgorithm (Bool × Point d) H (PersistentReply d) (Point d) S)
    (F : Z → Point d → ℝ) (tape : ℕ → Z) :
    (toFullJetStopping P).extendedCost (fun x z => richReply F z x) tape =
      P.extendedCost (separateSampleReply F) tape := by
  unfold PersistentStoppingAlgorithm.extendedCost
  apply iSup_congr
  intro n
  apply ite_congr _ (fun _ => rfl) (fun _ => rfl)
  simp only [PersistentStoppingAlgorithm.NoStopBefore,toFullJetStopping_stopOnRun]

theorem toFullJetStopping_cap_output {H S Z : Type*} {d : ℕ}
    (P : PersistentStoppingAlgorithm (Bool × Point d) H (PersistentReply d) (Point d) S)
    (F : Z → Point d → ℝ) (tape : ℕ → Z) (N : ℕ) :
    (toFullJetStopping P).cap.output N
      (lazyPersistentRun (toFullJetStopping P).cap.toQueryPolicy (fun x z => richReply F z x) tape N).1 =
    P.cap.output N (lazyPersistentRun P.cap.toQueryPolicy (separateSampleReply F) tape N).1 := by
  rw [PersistentStoppingAlgorithm.cap_run,PersistentStoppingAlgorithm.cap_run]
  change (persistentStopScan _ _ N).2 = (persistentStopScan _ _ N).2
  rw [show (toFullJetStopping P).stopOnRun (fun x z => richReply F z x) tape =
      P.stopOnRun (separateSampleReply F) tape from funext (toFullJetStopping_stopOnRun P F tape),
    show (toFullJetStopping P).outputAt (fun x z => richReply F z x) tape =
      P.outputAt (separateSampleReply F) tape from funext (toFullJetStopping_outputAt P F tape)]

theorem toFullJetStopping_finiteCapOutput {H S Z : Type} {d : ℕ}
    (P : PersistentStoppingAlgorithm (Bool × Point d) H (PersistentReply d) (Point d) S)
    (F : Z → Point d → ℝ) (N : ℕ) (table : Fin (N+1) → Z) :
    finiteCapOutput (toFullJetStopping P) (fun x z => richReply F z x) N table =
      finiteCapOutput P (separateSampleReply F) N table := by
  rw [finiteCapOutput_as_lazy,finiteCapOutput_as_lazy,toFullJetStopping_cap_output]

structure SeparateOperationallyMeasurable {d : ℕ} {H S Ξ : Type} [MeasurableSpace Ξ]
    (P : Ξ → PersistentStoppingAlgorithm (Bool × Point d) H (PersistentReply d) (Point d) S) : Prop where
  finite_output : ∀ (Z : Type) [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (F : Z → Point d → ℝ), (∀ z, ContDiff ℝ 2 (F z)) → ∀ N (table : Fin (N+1) → Z),
    Measurable (fun ξ => finiteCapOutput (P ξ) (separateSampleReply F) N table)
  stop_run : ∀ (Z : Type) [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (F : Z → Point d → ℝ), (∀ z, ContDiff ℝ 2 (F z)) → ∀ n,
    Measurable (fun w : Ξ × (ℕ → Z) => (P w.1).stopOnRun (separateSampleReply F) w.2 n)

theorem toFullJetStopping_operational {d : ℕ} {H S Ξ : Type} [MeasurableSpace Ξ]
    (P : Ξ → PersistentStoppingAlgorithm (Bool × Point d) H (PersistentReply d) (Point d) S)
    (hP : SeparateOperationallyMeasurable P) :
    OperationallyMeasurable (fun ξ => toFullJetStopping (P ξ)) := by
  constructor
  · intro Z _ _ _ F hF N table
    simpa only [toFullJetStopping_finiteCapOutput] using hP.finite_output Z F hF N table
  · intro Z _ _ _ F hF n
    simpa only [toFullJetStopping_stopOnRun] using hP.stop_run Z F hF n

end
end SampleReuse
