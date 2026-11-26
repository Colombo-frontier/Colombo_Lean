import SampleReuse.PersistentDeterministicBridge
import SampleReuse.PaddingOracle

open SecondOrder MeasureTheory
open scoped Classical ENNReal
namespace SampleReuse
noncomputable section

def projectStoppingAlgorithm {H S : Type} {m d : ℕ} (U : Point m →ₗᵢ[ℝ] Point d)
    (P : PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S) :
    PersistentStoppingAlgorithm (Point m) H (RichReply m) (Point m) S where
  toOracleAlgorithm := projectPersistentAlgorithm U P.toOracleAlgorithm
  stop := P.stop

theorem projectStopping_lazyRun {H S Z : Type} {m d : ℕ} (U : Point m →ₗᵢ[ℝ] Point d)
    (P : PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (F : Z → Point m → ℝ) (hF : ∀ z, ContDiff ℝ 2 (F z)) (tape : ℕ → Z) : ∀ n,
    lazyPersistentRun (projectStoppingAlgorithm U P).toQueryPolicy (fun x z => richReply F z x) tape n =
      lazyPersistentRun P.toQueryPolicy (fun x z => richReply (fun z => paddedLoss U (F z)) z x) tape n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [lazyPersistentRun]
    rw [ih]
    simp only [projectStoppingAlgorithm,projectPersistentAlgorithm,projectPersistentPolicy,
      richReply_padding U F hF]

theorem projectStopping_stop {H S Z : Type} {m d : ℕ} (U : Point m →ₗᵢ[ℝ] Point d)
    (P : PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (F : Z → Point m → ℝ) (hF : ∀ z, ContDiff ℝ 2 (F z)) (tape : ℕ → Z) (n : ℕ) :
    (projectStoppingAlgorithm U P).stopOnRun (fun x z => richReply F z x) tape n =
      P.stopOnRun (fun x z => richReply (fun z => paddedLoss U (F z)) z x) tape n := by
  unfold PersistentStoppingAlgorithm.stopOnRun PersistentStoppingAlgorithm.state
  rw [projectStopping_lazyRun U P F hF]
  rfl

theorem projectStopping_outputAt {H S Z : Type} {m d : ℕ} (U : Point m →ₗᵢ[ℝ] Point d)
    (P : PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (F : Z → Point m → ℝ) (hF : ∀ z, ContDiff ℝ 2 (F z)) (tape : ℕ → Z) (n : ℕ) :
    (projectStoppingAlgorithm U P).outputAt (fun x z => richReply F z x) tape n =
      isometryProjection U (P.outputAt (fun x z => richReply (fun z => paddedLoss U (F z)) z x) tape n) := by
  unfold PersistentStoppingAlgorithm.outputAt PersistentStoppingAlgorithm.state
  rw [projectStopping_lazyRun U P F hF]
  rfl

theorem projectStopping_halts {H S Z : Type} {m d : ℕ} (U : Point m →ₗᵢ[ℝ] Point d)
    (P : PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (F : Z → Point m → ℝ) (hF : ∀ z, ContDiff ℝ 2 (F z)) (tape : ℕ → Z) :
    (projectStoppingAlgorithm U P).Halts (fun x z => richReply F z x) tape ↔
      P.Halts (fun x z => richReply (fun z => paddedLoss U (F z)) z x) tape := by
  simp only [PersistentStoppingAlgorithm.Halts,projectStopping_stop U P F hF]

theorem projectStopping_cost {H S Z : Type} {m d : ℕ} (U : Point m →ₗᵢ[ℝ] Point d)
    (P : PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (F : Z → Point m → ℝ) (hF : ∀ z, ContDiff ℝ 2 (F z)) (tape : ℕ → Z) :
    (projectStoppingAlgorithm U P).cost (fun x z => richReply F z x) tape =
      P.cost (fun x z => richReply (fun z => paddedLoss U (F z)) z x) tape := by
  simp only [PersistentStoppingAlgorithm.cost,PersistentStoppingAlgorithm.Halts,projectStopping_stop U P F hF]

theorem projectStopping_output {H S Z : Type} {m d : ℕ} (U : Point m →ₗᵢ[ℝ] Point d)
    (P : PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (F : Z → Point m → ℝ) (hF : ∀ z, ContDiff ℝ 2 (F z)) (tape : ℕ → Z) :
    (projectStoppingAlgorithm U P).outputFor (fun x z => richReply F z x) tape =
      isometryProjection U (P.outputFor (fun x z => richReply (fun z => paddedLoss U (F z)) z x) tape) := by
  unfold PersistentStoppingAlgorithm.outputFor
  rw [projectStopping_outputAt U P F hF,projectStopping_cost U P F hF]

theorem projectStopping_extendedCost {H S Z : Type} {m d : ℕ} (U : Point m →ₗᵢ[ℝ] Point d)
    (P : PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (F : Z → Point m → ℝ) (hF : ∀ z, ContDiff ℝ 2 (F z)) (tape : ℕ → Z) :
    (projectStoppingAlgorithm U P).extendedCost (fun x z => richReply F z x) tape =
      P.extendedCost (fun x z => richReply (fun z => paddedLoss U (F z)) z x) tape := by
  simp only [PersistentStoppingAlgorithm.extendedCost,PersistentStoppingAlgorithm.NoStopBefore,
    projectStopping_stop U P F hF]
  apply iSup_congr
  intro n
  split_ifs <;> rfl

theorem persistentStopScan_map {O O' : Type*} (stop : ℕ → Bool) (output : ℕ → O) (f : O → O') :
    ∀ n, persistentStopScan stop (fun k => f (output k)) n =
      ((persistentStopScan stop output n).1,f (persistentStopScan stop output n).2) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [persistentStopScan,ih,persistentStopScan]
    split_ifs <;> rfl

theorem projectStopping_cap_output {H S Z : Type} {m d : ℕ} (U : Point m →ₗᵢ[ℝ] Point d)
    (P : PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (F : Z → Point m → ℝ) (hF : ∀ z, ContDiff ℝ 2 (F z)) (tape : ℕ → Z) (N : ℕ) :
    (projectStoppingAlgorithm U P).cap.output N
      (lazyPersistentRun (projectStoppingAlgorithm U P).cap.toQueryPolicy (fun x z => richReply F z x) tape N).1 =
      isometryProjection U (P.cap.output N
        (lazyPersistentRun P.cap.toQueryPolicy (fun x z => richReply (fun z => paddedLoss U (F z)) z x) tape N).1) := by
  rw [PersistentStoppingAlgorithm.cap_run,PersistentStoppingAlgorithm.cap_run]
  change (persistentStopScan _ _ N).2 = isometryProjection U (persistentStopScan _ _ N).2
  have hs := funext (projectStopping_stop U P F hF tape)
  have ho := funext (projectStopping_outputAt U P F hF tape)
  rw [hs,ho,persistentStopScan_map]

end
end SampleReuse
