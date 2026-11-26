import MatchingBounds1005.CUPGOrderedReplies
import MatchingBounds1005.CUPGCompiler
import MatchingBounds1005.CUPGCalibration

/-! The concrete deterministic first-order machine. Every phase uses 9N+3
calls, resets its response array, and retains the smallest observed gradient
norm. Queries and transitions depend only on stored oracle responses. -/
noncomputable section
open MeasureTheory

namespace MatchingBounds1005.CUPG

abbrev UpperState (d : ℕ) := PhaseData d × (Model.Space d × ℝ)
def phaseLength (N : ℕ) : ℕ := 9 * N + 3

def machineQuery {d : ℕ} (q α τ L ε : ℝ) (N t : ℕ) (s : UpperState d) : Model.Space d :=
  rawOrderedPhaseQuery q α τ L ε N (t % phaseLength N) s.1

def machinePush {d : ℕ} (N t : ℕ) (p : UpperState d × Model.Response d) : UpperState d :=
  ((p.1.1.1, Function.update p.1.1.2 (t % phaseLength N) p.2), p.1.2)

def machineFinish {d : ℕ} (q α τ L ε : ℝ) (N t : ℕ)
    (p : UpperState d × Model.Response d) : UpperState d :=
  let x := rawOrderedCandidate q α τ L ε N p.1.1
  let record := (x, ‖p.2.2‖)
  let best := if t + 1 = phaseLength N then record else chooseLowerReply record p.1.2
  ((x, fun _ => 0), best)

def machineStep {d : ℕ} (q α τ L ε : ℝ) (N t : ℕ)
    (p : UpperState d × Model.Response d) : UpperState d :=
  if (t + 1) % phaseLength N = 0 then machineFinish q α τ L ε N t p else machinePush N t p

theorem measurable_machineQuery {d : ℕ} (q α τ L ε : ℝ) (N t : ℕ) :
    Measurable (machineQuery (d := d) q α τ L ε N t) :=
  (measurable_rawOrderedPhaseQuery q α τ L ε N (t % phaseLength N)).comp measurable_fst

theorem measurable_machinePush {d : ℕ} (N t : ℕ) :
    Measurable (machinePush (d := d) N t) :=
  (measurable_fst.fst.fst.prodMk
    (measurable_update'.comp (measurable_fst.fst.snd.prodMk measurable_snd))).prodMk measurable_fst.snd

theorem measurable_machineFinish {d : ℕ} (q α τ L ε : ℝ) (N t : ℕ) :
    Measurable (machineFinish (d := d) q α τ L ε N t) := by
  have hx : Measurable (fun p : UpperState d × Model.Response d =>
      rawOrderedCandidate q α τ L ε N p.1.1) :=
    (measurable_rawOrderedCandidate (d := d) q α τ L ε N).comp measurable_fst.fst
  have hr : Measurable (fun p : UpperState d × Model.Response d =>
      (rawOrderedCandidate q α τ L ε N p.1.1, ‖p.2.2‖)) := hx.prodMk measurable_snd.snd.norm
  unfold machineFinish
  split_ifs
  · exact (hx.prodMk measurable_const).prodMk hr
  · exact (hx.prodMk measurable_const).prodMk
      (chooseLowerReply_measurable.comp (hr.prodMk measurable_fst.snd))

theorem measurable_machineStep {d : ℕ} (q α τ L ε : ℝ) (N t : ℕ) :
    Measurable (machineStep (d := d) q α τ L ε N t) := by
  unfold machineStep
  split_ifs
  · exact measurable_machineFinish q α τ L ε N t
  · exact measurable_machinePush N t

def upperMachine {d : ℕ} (q α τ L ε : ℝ) (N : ℕ) :
    RandomizedFO2003.Model.DeterministicMachine d (UpperState d) where
  initial := ((0, fun _ => 0), (0, 0))
  query := machineQuery q α τ L ε N
  step := machineStep q α τ L ε N
  output _ s := s.2.1
  measurable_query := measurable_machineQuery q α τ L ε N
  measurable_step := measurable_machineStep q α τ L ε N
  measurable_output _ := measurable_snd.fst

def upperAlgorithm (d : ℕ) (ε : ℝ) : Model.Algorithm d Unit :=
  let r := rootParameter ε
  compileMachine (upperMachine (r / 2) (r ^ 2) (r / 16) 4 ε (phaseCap r ε))

def upperBudget (ε : ℝ) : ℕ :=
  epochCap (rootParameter ε) * phaseLength (phaseCap (rootParameter ε) ε)

theorem upperBudget_bound {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) :
    (upperBudget ε : ℝ) ≤ 61920 * Model.rate ε * Real.log (2 / ε) := calibrated_totalCap hε hεone

end MatchingBounds1005.CUPG
