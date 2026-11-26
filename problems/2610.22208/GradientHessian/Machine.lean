import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
# Measurable mixed-query machines, with unbounded finite internal computation

A policy receives no input-dependent information except the selected oracle
replies. Mode 0 halts, 1 performs an uncharged internal step, 2 is an ordinary
query and 3 is a rich query. The output can be any point, whether queried or not.
The seed and initial state are fixed independently of the oracle.

No uniform internal-time bound is imposed. Finite cutoffs are modeled through
increasing measurable success events and their exact countable union.
-/

namespace GradientHessian.Machine

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

variable (Seed State X Y Z : Type*)
  [MeasurableSpace Seed] [MeasurableSpace State] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

structure Policy where
  initial : Seed → State
  mode : State → Fin 4
  point : State → X
  output : State → X
  think : State → State
  ordinaryNext : State × Y → State
  richNext : State × Z → State
  initial_measurable : Measurable initial
  mode_measurable : Measurable mode
  point_measurable : Measurable point
  output_measurable : Measurable output
  think_measurable : Measurable think
  ordinaryNext_measurable : Measurable ordinaryNext
  richNext_measurable : Measurable richNext

variable {Seed State X Y Z}

def Policy.step (P : Policy Seed State X Y Z) (ordinary : X → Y) (rich : X → Z)
    (s : State) : State :=
  if P.mode s = 0 then s
  else if P.mode s = 1 then P.think s
  else if P.mode s = 2 then P.ordinaryNext (s, ordinary (P.point s))
  else P.richNext (s, rich (P.point s))

def Policy.run (P : Policy Seed State X Y Z) (ordinary : X → Y) (rich : X → Z) :
    ℕ → Seed → State
  | 0 => P.initial
  | n + 1 => fun seed => P.step ordinary rich (P.run ordinary rich n seed)

theorem Policy.step_measurable (P : Policy Seed State X Y Z)
    {ordinary : X → Y} {rich : X → Z}
    (ho : Measurable ordinary) (hr : Measurable rich) :
    Measurable (P.step ordinary rich) := by
  apply Measurable.ite (P.mode_measurable (measurableSet_singleton 0)) measurable_id
  apply Measurable.ite (P.mode_measurable (measurableSet_singleton 1)) P.think_measurable
  apply Measurable.ite (P.mode_measurable (measurableSet_singleton 2))
  · exact P.ordinaryNext_measurable.comp
      (measurable_id.prodMk (ho.comp P.point_measurable))
  · exact P.richNext_measurable.comp
      (measurable_id.prodMk (hr.comp P.point_measurable))

theorem Policy.run_measurable (P : Policy Seed State X Y Z)
    {ordinary : X → Y} {rich : X → Z}
    (ho : Measurable ordinary) (hr : Measurable rich) (n : ℕ) :
    Measurable (P.run ordinary rich n) := by
  induction n with
  | zero => exact P.initial_measurable
  | succ n ih => exact (P.step_measurable ho hr).comp ih

theorem Policy.step_of_halt (P : Policy Seed State X Y Z)
    (ordinary : X → Y) (rich : X → Z) {s : State} (hs : P.mode s = 0) :
    P.step ordinary rich s = s := by simp [Policy.step, hs]

theorem Policy.run_after_halt (P : Policy Seed State X Y Z)
    (ordinary : X → Y) (rich : X → Z) (seed : Seed) {n : ℕ}
    (hn : P.mode (P.run ordinary rich n seed) = 0) (k : ℕ) :
    P.run ordinary rich (n + k) seed = P.run ordinary rich n seed := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ]
    change P.step ordinary rich (P.run ordinary rich (n + k) seed) = _
    rw [ih]
    exact P.step_of_halt ordinary rich hn

def Policy.ordinaryCount (P : Policy Seed State X Y Z)
    (ordinary : X → Y) (rich : X → Z) (n : ℕ) (seed : Seed) : ℕ :=
  ∑ i ∈ Finset.range n, if P.mode (P.run ordinary rich i seed) = 2 then 1 else 0

def Policy.richCount (P : Policy Seed State X Y Z)
    (ordinary : X → Y) (rich : X → Z) (n : ℕ) (seed : Seed) : ℕ :=
  ∑ i ∈ Finset.range n, if P.mode (P.run ordinary rich i seed) = 3 then 1 else 0

/-- Pathwise caps are checked at every prefix, including before termination. -/
def Policy.HasCaps (P : Policy Seed State X Y Z)
    (ordinary : X → Y) (rich : X → Z) (G H : ℕ) : Prop :=
  ∀ seed n, P.ordinaryCount ordinary rich n seed ≤ G ∧
    P.richCount ordinary rich n seed ≤ H

def Policy.Terminates (P : Policy Seed State X Y Z)
    (ordinary : X → Y) (rich : X → Z) : Prop :=
  ∀ seed, ∃ n, P.mode (P.run ordinary rich n seed) = 0

/-- Also allow almost-sure finite termination, so the eventual lower bound
covers this more permissive convention for randomized algorithms. Query caps
remain pathwise, including seeds in null sets. -/
def Policy.TerminatesAlmostSurely (P : Policy Seed State X Y Z)
    (ordinary : X → Y) (rich : X → Z) (μ : Measure Seed) : Prop :=
  ∀ᵐ seed ∂μ, ∃ n, P.mode (P.run ordinary rich n seed) = 0

theorem Policy.terminatesAlmostSurely_of_terminates (P : Policy Seed State X Y Z)
    (ordinary : X → Y) (rich : X → Z) (μ : Measure Seed)
    (h : P.Terminates ordinary rich) : P.TerminatesAlmostSurely ordinary rich μ :=
  Filter.Eventually.of_forall h

def Policy.successBy (P : Policy Seed State X Y Z)
    (ordinary : X → Y) (rich : X → Z) (good : Set X) (N : ℕ) : Set Seed :=
  {seed | ∃ n ≤ N, P.mode (P.run ordinary rich n seed) = 0 ∧
    P.output (P.run ordinary rich n seed) ∈ good}

def Policy.success (P : Policy Seed State X Y Z)
    (ordinary : X → Y) (rich : X → Z) (good : Set X) : Set Seed :=
  {seed | ∃ n, P.mode (P.run ordinary rich n seed) = 0 ∧
    P.output (P.run ordinary rich n seed) ∈ good}

theorem Policy.successBy_mono (P : Policy Seed State X Y Z)
    (ordinary : X → Y) (rich : X → Z) (good : Set X) :
    Monotone (P.successBy ordinary rich good) := by
  intro i j hij seed ⟨n, hn, hs⟩
  exact ⟨n, hn.trans hij, hs⟩

theorem Policy.success_eq_iUnion (P : Policy Seed State X Y Z)
    (ordinary : X → Y) (rich : X → Z) (good : Set X) :
    P.success ordinary rich good = ⋃ N, P.successBy ordinary rich good N := by
  ext seed
  simp only [Policy.success, Policy.successBy, mem_setOf_eq, mem_iUnion]
  constructor
  · rintro ⟨n, h⟩; exact ⟨n, n, le_rfl, h⟩
  · rintro ⟨_, n, _, h⟩; exact ⟨n, h⟩

theorem Policy.successBy_measurable (P : Policy Seed State X Y Z)
    {ordinary : X → Y} {rich : X → Z} {good : Set X}
    (ho : Measurable ordinary) (hr : Measurable rich) (hg : MeasurableSet good) (N : ℕ) :
    MeasurableSet (P.successBy ordinary rich good N) := by
  have hn : ∀ n, MeasurableSet {seed | P.mode (P.run ordinary rich n seed) = 0 ∧
      P.output (P.run ordinary rich n seed) ∈ good} := by
    intro n
    exact ((P.mode_measurable.comp (P.run_measurable ho hr n))
      (measurableSet_singleton 0)).inter
      ((P.output_measurable.comp (P.run_measurable ho hr n)) hg)
  have heq : P.successBy ordinary rich good N = ⋃ n : ℕ, ⋃ (_ : n ≤ N),
      {seed | P.mode (P.run ordinary rich n seed) = 0 ∧
        P.output (P.run ordinary rich n seed) ∈ good} := by
    ext seed
    simp [Policy.successBy, and_comm, and_left_comm, and_assoc]
  rw [heq]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun (_ : n ≤ N) => hn n

theorem Policy.success_measurable (P : Policy Seed State X Y Z)
    {ordinary : X → Y} {rich : X → Z} {good : Set X}
    (ho : Measurable ordinary) (hr : Measurable rich) (hg : MeasurableSet good) :
    MeasurableSet (P.success ordinary rich good) := by
  rw [P.success_eq_iUnion]
  exact MeasurableSet.iUnion (P.successBy_measurable ho hr hg)

/-- An input-independent finite computation cutoff loses arbitrarily little
success mass. This limit does not posit a uniform termination time. -/
theorem Policy.cutoff_success_tendsto (P : Policy Seed State X Y Z)
    (ordinary : X → Y) (rich : X → Z) (good : Set X) (μ : Measure Seed) :
    Tendsto (fun N => μ (P.successBy ordinary rich good N)) atTop
      (𝓝 (μ (P.success ordinary rich good))) := by
  rw [P.success_eq_iUnion]
  exact tendsto_measure_iUnion_atTop (P.successBy_mono ordinary rich good)

end GradientHessian.Machine
