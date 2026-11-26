import FreshGradientMinimax.ProgramBatch

/-! A program can use a transformed input and retain the original input
for a deterministic state update after sampling, without another oracle call. -/

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace OracleProgram
variable {dx dy : ℕ} {X Y Z W : Type}
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]

def precompose (P : OracleProgram dx dy X Y) (f : W → X) (hf : Measurable f) : OracleProgram dx dy W Y where
  Seed := P.Seed
  seedLaw := P.seedLaw
  State := P.State
  machine := P.machine
  init i := P.init i ∘ f
  init_measurable i := (P.init_measurable i).comp hf
  read := P.read
  read_measurable := P.read_measurable
  calls := P.calls

theorem precompose_branch (P : OracleProgram dx dy X Y) (f : W → X) (hf : Measurable f)
    (K : Kernel (Joint dx dy) (Joint dx dy)) (i : P.Seed) :
    (P.precompose f hf).branchKernel K i = (P.branchKernel K i).comap f hf := by
  rw [branchKernel_eq_map, P.branchKernel_eq_map]
  change ((P.machine i).runKernel (P.init i ∘ f) ((P.init_measurable i).comp hf) K (P.calls i)).map
    (fun s => (P.read i s, P.calls i)) = _
  rw [OracleMachine.runKernel_init_comp, Kernel.comap_map_comm _ hf ((P.read_measurable i).prodMk measurable_const)]

theorem precompose_law (P : OracleProgram dx dy X Y) (f : W → X) (hf : Measurable f)
    (K : Kernel (Joint dx dy) (Joint dx dy)) :
    (P.precompose f hf).lawKernel K = (P.lawKernel K).comap f hf := by
  apply Kernel.ext
  intro x
  apply Measure.ext
  intro A hA
  change mixtureKernel P.seedLaw ((P.precompose f hf).branchKernel K) x A = _
  rw [Kernel.comap_apply, lawKernel, mixtureKernel_apply _ _ _ hA, mixtureKernel_apply _ _ _ hA]
  simp_rw [P.precompose_branch f hf K, Kernel.comap_apply]

def update (P : OracleProgram dx dy X Y) (f : X × Y → Z) (hf : Measurable f) : OracleProgram dx dy X Z :=
  ((pure id measurable_id).pair P).map f hf

theorem update_law (P : OracleProgram dx dy X Y) (f : X × Y → Z) (hf : Measurable f)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] :
    (P.update f hf).lawKernel K = costedUpdateKernel (P.lawKernel K) f (fun _ => 0) := by
  rw [update, map_law, pair_law, pure_law]
  change (((Kernel.id.map (fun x : X => (x, (0 : ℕ)))) ×ₖ P.lawKernel K).map pairCost).map
    (fun z : (X × Y) × ℕ => (f z.1, z.2)) = _
  rw [Kernel.map_prod_eq _ _ (show Measurable (fun x : X => (x, (0 : ℕ))) from measurable_id.prodMk measurable_const),
    ← Kernel.map_comp_right _
      ((show Measurable (fun x : X => (x, (0 : ℕ))) from measurable_id.prodMk measurable_const).prodMap measurable_id)
      pairCost_measurable,
    ← Kernel.map_comp_right _
      (g := fun z : (X × Y) × ℕ => (f z.1, z.2))
      (pairCost_measurable.comp ((show Measurable (fun x : X => (x, (0 : ℕ))) from measurable_id.prodMk measurable_const).prodMap measurable_id))
      ((hf.comp measurable_fst).prodMk measurable_snd)]
  rfl

end OracleProgram
end FreshGradientMinimax
