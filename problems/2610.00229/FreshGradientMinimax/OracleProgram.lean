import FreshGradientMinimax.LabelMachines

/-! A program records only executable mathematical data: a countable
probability seed, a one-original-call state machine, initialization, a
measurable internal output, and a seed-dependent finite duration. There
are no assumed distributional or complexity conclusions in this record.
Its abstract branch mixture equals the stopped law of one compiled policy. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

structure OracleProgram (dx dy : ℕ) (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] where
  Seed : Type
  [seedMeasurable : MeasurableSpace Seed]
  [seedCountable : Countable Seed]
  [seedSingleton : MeasurableSingletonClass Seed]
  seedLaw : Measure Seed
  [seedProbability : IsProbabilityMeasure seedLaw]
  State : Type
  [stateMeasurable : MeasurableSpace State]
  machine : Seed → OracleMachine dx dy State
  init : Seed → X → State
  init_measurable : ∀ i, Measurable (init i)
  read : Seed → State → Y
  read_measurable : ∀ i, Measurable (read i)
  calls : Seed → ℕ

attribute [instance] OracleProgram.seedMeasurable OracleProgram.seedCountable OracleProgram.seedSingleton
  OracleProgram.seedProbability OracleProgram.stateMeasurable

namespace OracleProgram
variable {dx dy : ℕ} {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
variable (P : OracleProgram dx dy X Y)

def branchKernel (K : Kernel (Joint dx dy) (Joint dx dy)) (i : P.Seed) : Kernel X (Y × ℕ) :=
  taggedKernel (((P.machine i).runKernel (P.init i) (P.init_measurable i) K (P.calls i)).map (P.read i)) (P.calls i)

instance branchKernel_markov (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (i : P.Seed) :
    IsMarkovKernel (P.branchKernel K i) := by
  letI := Kernel.IsMarkovKernel.map ((P.machine i).runKernel (P.init i) (P.init_measurable i) K (P.calls i))
    (P.read_measurable i)
  unfold branchKernel
  infer_instance

def lawKernel (K : Kernel (Joint dx dy) (Joint dx dy)) : Kernel X (Y × ℕ) :=
  mixtureKernel P.seedLaw (P.branchKernel K)

instance lawKernel_markov (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] :
    IsMarkovKernel (P.lawKernel K) := by unfold lawKernel; infer_instance

def policy : Algorithm dx dy (X × P.Seed) :=
  (OracleMachine.labelSelect P.machine).compile (OracleMachine.labelInitial P.init)
    (OracleMachine.labelInitial_measurable P.init P.init_measurable)

def method (x : X) : RandomizedAlgorithm dx dy where
  Seed := X × P.Seed
  seedLaw := inputSeedKernel P.seedLaw x
  policy := P.policy

def stoppedKernel (K : Kernel (Joint dx dy) (Joint dx dy)) : Kernel (X × P.Seed) (Y × ℕ) :=
  (OracleMachine.labelSelect P.machine).seedStoppedKernel
    (OracleMachine.labelInitial P.init) (OracleMachine.labelInitial_measurable P.init P.init_measurable) K
    (fun s => P.calls s.2) ((measurable_of_countable P.calls).comp measurable_snd)
    (OracleMachine.labelRead P.read)

def originalKernel (K : Kernel (Joint dx dy) (Joint dx dy)) : Kernel X (Y × ℕ) :=
  P.stoppedKernel K ∘ₖ inputSeedKernel P.seedLaw

theorem stoppedKernel_eq (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] :
    P.stoppedKernel K = labelKernel (P.branchKernel K) := by
  apply Kernel.ext
  rintro ⟨x, i⟩
  rw [stoppedKernel, OracleMachine.labelSelect_stopped_apply _ _ P.init_measurable K P.calls P.read P.read_measurable]
  change _ = P.branchKernel K i x
  rw [branchKernel, taggedKernel, ← Kernel.map_comp_right _ (f := P.read i)
    (g := fun y : Y => (y, P.calls i)) (P.read_measurable i) (measurable_id.prodMk measurable_const),
    Kernel.map_apply (f := (fun y : Y => (y, P.calls i)) ∘ P.read i) _
      ((P.read_measurable i).prodMk measurable_const)]
  rfl

theorem originalKernel_eq_law (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] :
    P.originalKernel K = P.lawKernel K := by
  rw [originalKernel, P.stoppedKernel_eq]
  rfl

end OracleProgram
end FreshGradientMinimax
