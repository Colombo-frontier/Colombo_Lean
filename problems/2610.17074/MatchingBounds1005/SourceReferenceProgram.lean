import MatchingBounds1005.ReferenceStateFinish
import MatchingBounds1005.ReadoutCalendar

/-!
# A fully concrete accessible Gaussian-reference source program

The program stores each directly disclosed unit readout and the linear
coefficient. Every physical query computes the simultaneous normalized
Gaussian tensor channels, reconstructs value and gradient from the physical
matrix response and disclosed taper corrections, and advances the original
algorithm exactly once. The final candidate is frozen without an oracle call.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff

namespace MatchingBounds1005.SourceReferenceProgram
open GaussianVector ReferenceState ScheduledHaar AccessibleReferenceCompiler
open TensorGeometry hiding Vec

structure Parameters (d N : ℕ) where
  Q : Vec d →L[ℝ] Vec d
  c : Vec d
  b : Fin N → Vec d
  disclosure : Fin N → ℕ
  τ : ℝ
  r : ℝ
  a : ℝ
  σ₃ : ℝ
  σ₄ : ℝ
  R : ℝ
  η : ℝ

variable {Seed : Type} [MeasurableSpace Seed] {d N H : ℕ}

def correction (P : Parameters d N) (p : (Fin N → Vec d) × Vec d) : Model.Response d :=
  Model.oracle (correctionSum p.1 P.τ P.r P.a Finset.univ) p.2

theorem correction_measurable (P : Parameters d N) : Measurable (correction P) :=
  correctionSum_oracle_measurable P.τ P.r P.a Finset.univ

def readoutUpdate (i : Fin N) : Update (E := Vec d) (State Seed d H N) :=
  ⟨setReadout i, setReadout_measurable i⟩

def linearUpdate : Update (E := Vec d) (State Seed d H N) :=
  ⟨setLinear, setLinear_measurable⟩

def query (P : Parameters d N) (A : Model.Algorithm d Seed) (time : ℕ) :
    PhysicalRequest (E := Vec d) (State Seed d H N) × Update (E := Vec d) (State Seed d H N) :=
  sourceQueryCommand A (10 * P.τ * N) P.τ P.a P.σ₃ P.σ₄ P.R P.η
    (correction P) (correction_measurable P) (time - 1)

def candidatePoint (P : Parameters d N) (A : Model.Algorithm d Seed) (time : ℕ)
    (s : State Seed d H N) : Vec d := radial P.R (A.output (time - 1) s.1.1 (fun i => s.2.2.1 i.val))

theorem candidatePoint_measurable (P : Parameters d N) (A : Model.Algorithm d Seed) (time : ℕ) :
    Measurable (candidatePoint (H := H) P A time) :=
  (radial_contDiff (E := Vec d) P.R ∞).continuous.measurable.comp
    ((A.output_measurable (time - 1)).comp (algorithmInput_measurable (time - 1)))

def candidate (P : Parameters d N) (A : Model.Algorithm d Seed) (time : ℕ) :
    PhysicalRequest (E := Vec d) (State Seed d H N) × Update (E := Vec d) (State Seed d H N) :=
  (⟨candidatePoint P A time, candidatePoint_measurable P A time⟩, ⟨Prod.fst, measurable_fst⟩)

def commands (P : Parameters d N) (H : ℕ) : List SourceKind :=
  .disclose :: ReadoutCalendar.kinds P.disclosure 1 H

def machine (P : Parameters d N) (A : Model.Algorithm d Seed) :
    Machine (E := Vec d) (S := State Seed d H N) (commands P H) :=
  ((P.c, linearUpdate), ReadoutCalendar.machine P.b P.disclosure readoutUpdate
    (query P A) (candidate P A) 1 H)

def plan (P : Parameters d N) (A : Model.Algorithm d Seed) :
    SourcePolicy (E := Vec d) (commands P H) (Seed × FiniteGaussianSampler.Noise (TensorChannelRows.jointDim d) H) :=
  AccessibleReferenceCompiler.compile (commands P H) (machine P A) initial initial_measurable

def execute (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Vec d →L[ℝ] Vec d)
    (s : Seed × FiniteGaussianSampler.Noise (TensorChannelRows.jointDim d) H) : State Seed d H N :=
  ReadoutCalendar.runCalendar P.b P.disclosure readoutUpdate (query P A) (candidate P A) P.Q U 1 H
    (setLinear (initial s, U P.c))

/-- An actual SourcePolicy, started from independent private seeds, realizes
the complete concrete reference state-machine semantics exactly. -/
theorem plan_correct (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Vec d →L[ℝ] Vec d)
    (s : Seed × FiniteGaussianSampler.Noise (TensorChannelRows.jointDim d) H) :
    AccessibleReferenceCompiler.decode (commands P H) (machine P A) initial
      ((plan P A).run (commands P H) P.Q U s) = execute P A U s := by
  rw [plan, AccessibleReferenceCompiler.compile_correct]
  change AccessibleReferenceCompiler.run (ReadoutCalendar.kinds P.disclosure 1 H)
    (ReadoutCalendar.machine P.b P.disclosure readoutUpdate (query P A) (candidate P A) 1 H)
    P.Q U (setLinear (initial s, U P.c)) = _
  exact ReadoutCalendar.machine_run _ _ _ _ _ _ _ _ _ _

end MatchingBounds1005.SourceReferenceProgram
