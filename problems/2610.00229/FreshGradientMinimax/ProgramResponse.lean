import FreshGradientMinimax.MachineResponse
import FreshGradientMinimax.ParameterCarry

/-! Whole-program response adaptation with a continuously varying known
parameter. The exact joint output/count law is preserved on every fiber;
the parameter is ordinary state and may be correlated with the input. -/

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace OracleProgram
variable {dx dy : ℕ} {X Y Θ : Type}
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Θ]

def adaptResponses (P : OracleProgram dx dy X Y)
    (T : Θ × (Joint dx dy × Joint dx dy) → Joint dx dy) (hT : Measurable T) :
    OracleProgram dx dy (Θ × X) (Θ × Y) where
  Seed := P.Seed
  seedLaw := P.seedLaw
  State := Θ × P.State
  machine i := (P.machine i).adaptResponses T hT
  init i z := (z.1, P.init i z.2)
  init_measurable i := measurable_fst.prodMk ((P.init_measurable i).comp measurable_snd)
  read i z := (z.1, P.read i z.2)
  read_measurable i := measurable_fst.prodMk ((P.read_measurable i).comp measurable_snd)
  calls := P.calls

theorem adaptResponses_branch (P : OracleProgram dx dy X Y)
    (T : Θ × (Joint dx dy × Joint dx dy) → Joint dx dy) (hT : Measurable T)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (θ : Θ) (i : P.Seed) :
    ((P.adaptResponses T hT).branchKernel K i).comap (fun x => (θ, x)) measurable_prodMk_left =
      (P.branchKernel (responseTransformKernel K (fun p => T (θ, p))) i).map (costedMap (fun y => (θ, y))) := by
  rw [branchKernel_eq_map, branchKernel_eq_map]
  dsimp only [adaptResponses]
  rw [Kernel.comap_map_comm _ (f := fun x : X => (θ, x))
    (g := fun s : Θ × P.State => ((s.1, P.read i s.2), P.calls i)) measurable_prodMk_left
    ((measurable_fst.prodMk ((P.read_measurable i).comp measurable_snd)).prodMk measurable_const)]
  rw [← OracleMachine.runKernel_init_comp]
  change (((P.machine i).adaptResponses T hT).runKernel (fun x => (θ, P.init i x)) _ K (P.calls i)).map
    (fun s => ((s.1, P.read i s.2), P.calls i)) = _
  rw [OracleMachine.adaptResponses_run_fixed,
    ← Kernel.map_comp_right _ (f := fun s : P.State => (θ, s))
      (g := fun s : Θ × P.State => ((s.1, P.read i s.2), P.calls i)) measurable_prodMk_left
      ((measurable_fst.prodMk ((P.read_measurable i).comp measurable_snd)).prodMk measurable_const),
    ← Kernel.map_comp_right _ (f := fun s : P.State => (P.read i s, P.calls i))
      (g := costedMap (fun y : Y => (θ, y))) ((P.read_measurable i).prodMk measurable_const)
      (costedMap_measurable measurable_prodMk_left)]
  rfl

theorem adaptResponses_law (P : OracleProgram dx dy X Y)
    (T : Θ × (Joint dx dy × Joint dx dy) → Joint dx dy) (hT : Measurable T)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (θ : Θ) :
    ((P.adaptResponses T hT).lawKernel K).comap (fun x => (θ, x)) measurable_prodMk_left =
      (P.lawKernel (responseTransformKernel K (fun p => T (θ, p)))).map (costedMap (fun y => (θ, y))) := by
  apply Kernel.ext
  intro x
  apply Measure.ext
  intro A hA
  rw [Kernel.comap_apply, Kernel.map_apply' _ (costedMap_measurable measurable_prodMk_left) _ hA]
  change mixtureKernel P.seedLaw ((P.adaptResponses T hT).branchKernel K) (θ, x) A =
    mixtureKernel P.seedLaw (P.branchKernel (responseTransformKernel K (fun p => T (θ, p)))) x
      (costedMap (fun y => (θ, y)) ⁻¹' A)
  rw [mixtureKernel_apply _ _ _ hA, mixtureKernel_apply _ _ _
    ((costedMap_measurable measurable_prodMk_left) hA)]
  apply lintegral_congr
  intro i
  have h := congrArg (fun L : Kernel X ((Θ × Y) × ℕ) => L x A) (P.adaptResponses_branch T hT K θ i)
  dsimp only at h
  rw [Kernel.comap_apply, Kernel.map_apply' _ (costedMap_measurable measurable_prodMk_left) _ hA] at h
  exact h

theorem adaptResponses_original (P : OracleProgram dx dy X Y)
    (T : Θ × (Joint dx dy × Joint dx dy) → Joint dx dy) (hT : Measurable T)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (θ : Θ) :
    ((P.adaptResponses T hT).originalKernel K).comap (fun x => (θ, x)) measurable_prodMk_left =
      (P.originalKernel (responseTransformKernel K (fun p => T (θ, p)))).map (costedMap (fun y => (θ, y))) := by
  letI : IsMarkovKernel (responseTransformKernel K (fun p => T (θ, p))) :=
    responseTransformKernel_markov K _ (hT.comp measurable_prodMk_left)
  rw [originalKernel_eq_law, originalKernel_eq_law, adaptResponses_law]

end OracleProgram
end FreshGradientMinimax
