import FreshGradientMinimax.ProgramResult
import FreshGradientMinimax.MachineCap

/-! A program with seed-dependent finite duration gives a genuine fixed
budget RandomizedAlgorithm. The exact output law is its stopped-history
law with over-budget outcomes replaced by zero. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {dx dy : ℕ} {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]

def cappedRead (f : Y → Euclid dx) (N : ℕ) (p : Y × ℕ) : Euclid dx := if p.2 ≤ N then f p.1 else 0

theorem cappedRead_measurable {f : Y → Euclid dx} (hf : Measurable f) (N : ℕ) :
    Measurable (cappedRead f N) :=
  Measurable.ite (measurableSet_le measurable_snd measurable_const) (hf.comp measurable_fst) measurable_const

namespace OracleProgram

def budgetMachine (P : OracleProgram dx dy X Y) (f : Y → Euclid dx) (hf : Measurable f) :
    OracleMachine dx dy (P.State × P.Seed) :=
  OracleMachine.labelSelect (fun i => (P.machine i).capped (P.calls i) (f ∘ P.read i) (hf.comp (P.read_measurable i)))

def budgetPolicy (P : OracleProgram dx dy X Y) (f : Y → Euclid dx) (hf : Measurable f) :
    Algorithm dx dy (X × P.Seed) :=
  (P.budgetMachine f hf).compile (OracleMachine.labelInitial P.init)
    (OracleMachine.labelInitial_measurable P.init P.init_measurable)

def budgetMethod (P : OracleProgram dx dy X Y) (f : Y → Euclid dx) (hf : Measurable f) (x : X) :
    RandomizedAlgorithm dx dy where
  Seed := X × P.Seed
  seedLaw := inputSeedKernel P.seedLaw x
  policy := P.budgetPolicy f hf

theorem budgetPolicy_output_apply (P : OracleProgram dx dy X Y) (f : Y → Euclid dx) (hf : Measurable f)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (N : ℕ) (x : X) (i : P.Seed) :
    (P.budgetPolicy f hf).outputKernel K N (x, i) = (P.branchKernel K i x).map (cappedRead f N) := by
  rw [budgetPolicy, OracleMachine.compiled_outputKernel,
    Kernel.map_apply _ ((P.budgetMachine f hf).output_measurable N), budgetMachine,
    OracleMachine.labelSelect_run_apply,
    Measure.map_map (f := fun s : P.State => (s, i))
      (g := (OracleMachine.labelSelect (fun j : P.Seed => (P.machine j).capped
        (P.calls j) (f ∘ P.read j) (hf.comp (P.read_measurable j)))).output N)
      (OracleMachine.output_measurable _ N) (measurable_id.prodMk measurable_const)]
  change (((P.machine i).capped (P.calls i) (f ∘ P.read i) (hf.comp (P.read_measurable i))).runKernel
    (P.init i) (P.init_measurable i) K N x).map
      (((P.machine i).capped (P.calls i) (f ∘ P.read i) (hf.comp (P.read_measurable i))).output N) = _
  have h := congrArg (fun R : Kernel X (Euclid dx) => R x)
    ((P.machine i).capped_output (P.calls i) (f ∘ P.read i) (hf.comp (P.read_measurable i))
      (P.init i) (P.init_measurable i) K N)
  dsimp only at h
  rw [Kernel.map_apply _ (OracleMachine.output_measurable _ N)] at h
  rw [h, branchKernel_apply]
  have hm : Measurable (fun y : Euclid dx => if P.calls i ≤ N then y else 0) := by
    split_ifs; exact measurable_id; exact measurable_const
  rw [Kernel.map_apply _ hm, Kernel.map_apply _ (hf.comp (P.read_measurable i)),
    Measure.map_map hm (hf.comp (P.read_measurable i)),
    Measure.map_map (cappedRead_measurable hf N) ((P.read_measurable i).prodMk measurable_const)]
  rfl

theorem budgetPolicy_outputKernel (P : OracleProgram dx dy X Y) (f : Y → Euclid dx) (hf : Measurable f)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (N : ℕ) :
    (P.budgetPolicy f hf).outputKernel K N = labelKernel (fun i => (P.branchKernel K i).map (cappedRead f N)) := by
  apply Kernel.ext
  rintro ⟨x, i⟩
  exact (P.budgetPolicy_output_apply f hf K N x i).trans (Kernel.map_apply _ (cappedRead_measurable hf N) x).symm

theorem budgetMethod_outputLaw (P : OracleProgram dx dy X Y) (f : Y → Euclid dx) (hf : Measurable f)
    (x : X) (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (N : ℕ) :
    (P.budgetMethod f hf x).outputLaw K N = (P.originalKernel K x).map (cappedRead f N) := by
  change (P.budgetPolicy f hf).outputKernel K N ∘ₘ inputSeedKernel P.seedLaw x = _
  rw [P.budgetPolicy_outputKernel]
  change mixtureKernel P.seedLaw (fun i => (P.branchKernel K i).map (cappedRead f N)) x = _
  rw [← mixtureKernel_map _ _ _ (cappedRead_measurable hf N),
    Kernel.map_apply _ (cappedRead_measurable hf N), originalKernel_eq_law]
  rfl

end OracleProgram
end FreshGradientMinimax
