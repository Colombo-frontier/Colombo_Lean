import MatchingBounds1005.VisibleReadouts
import MatchingBounds1005.AccessibleReferenceCompiler

/-!
# Direct-readout disclosure calendar and its genuine SourcePolicy compiler

Each readout is disclosed only at its deterministic layer. Disclosures do
not advance the query clock. A single candidate follows the physical query
rounds. The linear coefficient can be prepended as one initial disclosure.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace MatchingBounds1005.ReadoutCalendar
open GaussianVector ScheduledHaar AccessibleReferenceCompiler

universe u
variable {S : Type u} [MeasurableSpace S] {d N : ℕ}

def prependKinds (xs : List (Fin N)) (w : List SourceKind) : List SourceKind :=
  xs.map (fun _ => SourceKind.disclose) ++ w

def prependMachine (b : Fin N → Vec d) (update : Fin N → Update (E := Vec d) S) :
    (xs : List (Fin N)) → (w : List SourceKind) → Machine (E := Vec d) (S := S) w →
      Machine (E := Vec d) (S := S) (prependKinds xs w)
  | [], _, M => M
  | i :: xs, w, M => ((b i, update i), prependMachine b update xs w M)

def revealState (b : Fin N → Vec d) (update : Fin N → Update (E := Vec d) S)
    (U : Vec d →L[ℝ] Vec d) : List (Fin N) → S → S
  | [], s => s
  | i :: xs, s => revealState b update U xs ((update i).next (s, U (b i)))

theorem prependMachine_run (b : Fin N → Vec d) (update : Fin N → Update (E := Vec d) S)
    (xs : List (Fin N)) (w : List SourceKind) (M : Machine (E := Vec d) (S := S) w)
    (Q U : Vec d →L[ℝ] Vec d) (s : S) :
    AccessibleReferenceCompiler.run (prependKinds xs w) (prependMachine b update xs w M) Q U s =
      AccessibleReferenceCompiler.run w M Q U (revealState b update U xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons i xs ih => exact ih _

def kinds (τ : Fin N → ℕ) : ℕ → ℕ → List SourceKind
  | _, 0 => [.candidate]
  | start, rounds + 1 => prependKinds (VisibleReadouts.due τ start) (.query :: kinds τ (start + 1) rounds)

def machine (b : Fin N → Vec d) (τ : Fin N → ℕ)
    (update : Fin N → Update (E := Vec d) S)
    (query : ℕ → PhysicalRequest (E := Vec d) S × Update (E := Vec d) S)
    (candidate : ℕ → PhysicalRequest (E := Vec d) S × Update (E := Vec d) S) :
    (start rounds : ℕ) → Machine (E := Vec d) (S := S) (kinds τ start rounds)
  | start, 0 => (candidate start, PUnit.unit)
  | start, rounds + 1 => prependMachine b update (VisibleReadouts.due τ start)
      (.query :: kinds τ (start + 1) rounds)
      (query start, machine b τ update query candidate (start + 1) rounds)

def runCalendar (b : Fin N → Vec d) (τ : Fin N → ℕ)
    (update : Fin N → Update (E := Vec d) S)
    (query : ℕ → PhysicalRequest (E := Vec d) S × Update (E := Vec d) S)
    (candidate : ℕ → PhysicalRequest (E := Vec d) S × Update (E := Vec d) S)
    (Q U : Vec d →L[ℝ] Vec d) : ℕ → ℕ → S → S
  | start, 0, s => (candidate start).2.next (s, (candidate start).1.point s)
  | start, rounds + 1, s =>
      let s' := revealState b update U (VisibleReadouts.due τ start) s
      runCalendar b τ update query candidate Q U (start + 1) rounds
        ((query start).2.next (s', U (Q (U.adjoint ((query start).1.point s')))))

theorem machine_run (b : Fin N → Vec d) (τ : Fin N → ℕ)
    (update : Fin N → Update (E := Vec d) S)
    (query : ℕ → PhysicalRequest (E := Vec d) S × Update (E := Vec d) S)
    (candidate : ℕ → PhysicalRequest (E := Vec d) S × Update (E := Vec d) S)
    (Q U : Vec d →L[ℝ] Vec d) (start rounds : ℕ) (s : S) :
    AccessibleReferenceCompiler.run (kinds τ start rounds)
      (machine b τ update query candidate start rounds) Q U s =
        runCalendar b τ update query candidate Q U start rounds s := by
  induction rounds generalizing start s with
  | zero => rfl
  | succ rounds ih =>
      change AccessibleReferenceCompiler.run
        (prependKinds (VisibleReadouts.due τ start) (.query :: kinds τ (start + 1) rounds))
        (prependMachine b update (VisibleReadouts.due τ start)
          (.query :: kinds τ (start + 1) rounds)
          (query start, machine b τ update query candidate (start + 1) rounds)) Q U s = _
      rw [prependMachine_run]
      exact ih _ _

/-- The direct-readout calendar is an actual source policy. Every nonlinear
or Gaussian computation remains inside measurable private state updates. -/
theorem compiled_calendar (b : Fin N → Vec d) (τ : Fin N → ℕ)
    (update : Fin N → Update (E := Vec d) S)
    (query : ℕ → PhysicalRequest (E := Vec d) S × Update (E := Vec d) S)
    (candidate : ℕ → PhysicalRequest (E := Vec d) S × Update (E := Vec d) S)
    (Q U : Vec d →L[ℝ] Vec d) (start rounds : ℕ) (s : S) :
    let M := machine b τ update query candidate start rounds
    AccessibleReferenceCompiler.decode (kinds τ start rounds) M id
      ((AccessibleReferenceCompiler.compile (kinds τ start rounds) M id measurable_id).run
        (kinds τ start rounds) Q U s) =
          runCalendar b τ update query candidate Q U start rounds s := by
  dsimp only
  rw [AccessibleReferenceCompiler.compile_correct]
  exact machine_run b τ update query candidate Q U start rounds s

end MatchingBounds1005.ReadoutCalendar
