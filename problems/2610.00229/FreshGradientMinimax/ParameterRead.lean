import FreshGradientMinimax.ProgramUpdate

/-! A continuously varying, known parameter may affect a program's readout.
The parameter is carried as ordinary state, not as a countable random seed.
Fixing it recovers exactly the corresponding original-query program. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace OracleProgram
variable {dx dy : ℕ} {X Y Z Θ : Type}
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace Θ]

def withRead (P : OracleProgram dx dy X Y) (g : P.Seed → P.State → Z)
    (hg : ∀ i, Measurable (g i)) : OracleProgram dx dy X Z where
  Seed := P.Seed
  seedLaw := P.seedLaw
  State := P.State
  machine := P.machine
  init := P.init
  init_measurable := P.init_measurable
  read := g
  read_measurable := hg
  calls := P.calls

def parameterRead (P : OracleProgram dx dy X Y) (g : P.Seed → Θ × P.State → Z)
    (hg : ∀ i, Measurable (g i)) : OracleProgram dx dy (Θ × X) Z where
  Seed := P.Seed
  seedLaw := P.seedLaw
  State := Θ × P.State
  machine i := (P.machine i).carryLeft
  init i z := (z.1, P.init i z.2)
  init_measurable i := measurable_fst.prodMk ((P.init_measurable i).comp measurable_snd)
  read := g
  read_measurable := hg
  calls := P.calls

theorem parameterRead_branch (P : OracleProgram dx dy X Y)
    (g : P.Seed → Θ × P.State → Z) (hg : ∀ i, Measurable (g i))
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (θ : Θ) (i : P.Seed) :
    ((P.parameterRead g hg).branchKernel K i).comap (fun x => (θ, x)) measurable_prodMk_left =
      (P.withRead (fun j s => g j (θ, s)) (fun j => (hg j).comp measurable_prodMk_left)).branchKernel K i := by
  rw [branchKernel_eq_map, branchKernel_eq_map]
  dsimp only [parameterRead, withRead]
  rw [Kernel.comap_map_comm _ measurable_prodMk_left ((hg i).prodMk measurable_const)]
  change (((P.machine i).carryLeft.runKernel (fun z : Θ × X => (z.1, P.init i z.2))
    _ K (P.calls i)).comap (fun x => (θ, x)) measurable_prodMk_left).map
      (fun s => (g i s, P.calls i)) = _
  rw [← OracleMachine.runKernel_init_comp]
  change (((P.machine i).carryLeft.runKernel (fun x => (θ, P.init i x))
    _ K (P.calls i)).map (fun s => (g i s, P.calls i))) = _
  rw [OracleMachine.carryLeft_run_fixed, ← Kernel.map_comp_right _
    (f := fun s : P.State => (θ, s)) (g := fun s : Θ × P.State => (g i s, P.calls i))
    measurable_prodMk_left ((hg i).prodMk measurable_const)]
  rfl

theorem parameterRead_law (P : OracleProgram dx dy X Y)
    (g : P.Seed → Θ × P.State → Z) (hg : ∀ i, Measurable (g i))
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (θ : Θ) :
    ((P.parameterRead g hg).lawKernel K).comap (fun x => (θ, x)) measurable_prodMk_left =
      (P.withRead (fun j s => g j (θ, s)) (fun j => (hg j).comp measurable_prodMk_left)).lawKernel K := by
  apply Kernel.ext
  intro x
  apply Measure.ext
  intro A hA
  change mixtureKernel P.seedLaw ((P.parameterRead g hg).branchKernel K) (θ, x) A =
    mixtureKernel P.seedLaw ((P.withRead (fun j s => g j (θ, s)) _).branchKernel K) x A
  rw [mixtureKernel_apply _ _ _ hA, mixtureKernel_apply _ _ _ hA]
  apply lintegral_congr
  intro i
  exact congrArg (fun L : Kernel X (Z × ℕ) => L x A) (P.parameterRead_branch g hg K θ i)

theorem parameterRead_original (P : OracleProgram dx dy X Y)
    (g : P.Seed → Θ × P.State → Z) (hg : ∀ i, Measurable (g i))
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (θ : Θ) :
    ((P.parameterRead g hg).originalKernel K).comap (fun x => (θ, x)) measurable_prodMk_left =
      (P.withRead (fun j s => g j (θ, s)) (fun j => (hg j).comp measurable_prodMk_left)).originalKernel K := by
  rw [originalKernel_eq_law, originalKernel_eq_law, parameterRead_law]

end OracleProgram
end FreshGradientMinimax
