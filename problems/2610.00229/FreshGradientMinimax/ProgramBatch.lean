import FreshGradientMinimax.ProgramOperations

/-! Independent program pairs and minibatch averages, with each component
executed sequentially at its own seed-dependent original-query horizon. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {I J X Y Z : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
variable [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

theorem mixtureKernel_pair (μ : Measure I) [IsProbabilityMeasure μ] (ν : Measure J) [IsProbabilityMeasure ν]
    (L : I → Kernel X Y) [∀ i, IsMarkovKernel (L i)] (R : J → Kernel X Z) [∀ j, IsMarkovKernel (R j)] :
    mixtureKernel μ L ×ₖ mixtureKernel ν R = mixtureKernel (μ.prod ν) (fun s => L s.1 ×ₖ R s.2) := by
  apply Kernel.ext
  intro x
  apply Measure.ext
  intro A hA
  rw [Kernel.prod_apply, Measure.prod_apply hA,
    mixtureKernel_lintegral μ L x _ (measurable_measure_prodMk_left hA),
    mixtureKernel_apply (μ.prod ν) _ x hA,
    lintegral_prod _ (measurable_of_countable _).aemeasurable]
  apply lintegral_congr
  intro i
  simp_rw [mixtureKernel_apply ν R x (measurable_prodMk_left hA), Kernel.prod_apply, Measure.prod_apply hA]
  apply lintegral_lintegral_swap
  exact (measurable_from_prod_countable (fun j => measurable_measure_prodMk_left (ν := R j x) hA)).aemeasurable

def pairCost (z : (Y × ℕ) × (Z × ℕ)) : (Y × Z) × ℕ := ((z.1.1, z.2.1), z.1.2 + z.2.2)

theorem pairCost_measurable : Measurable (pairCost (Y := Y) (Z := Z)) :=
  (measurable_fst.fst.prodMk measurable_snd.fst).prodMk (measurable_fst.snd.add measurable_snd.snd)

namespace OracleProgram
variable {dx dy d : ℕ} {X Y Z : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

def pair (P : OracleProgram dx dy X Y) (Q : OracleProgram dx dy X Z) : OracleProgram dx dy X (Y × Z) where
  Seed := P.Seed × Q.Seed
  seedLaw := P.seedLaw.prod Q.seedLaw
  State := P.State × Q.State
  machine s := (P.machine s.1).independentPair (Q.machine s.2) (P.calls s.1)
  init s x := (P.init s.1 x, Q.init s.2 x)
  init_measurable s := (P.init_measurable s.1).prodMk (Q.init_measurable s.2)
  read s z := (P.read s.1 z.1, Q.read s.2 z.2)
  read_measurable s := ((P.read_measurable s.1).comp measurable_fst).prodMk ((Q.read_measurable s.2).comp measurable_snd)
  calls s := P.calls s.1 + Q.calls s.2

theorem branchKernel_eq_map (P : OracleProgram dx dy X Y) (K : Kernel (Joint dx dy) (Joint dx dy))
    (i : P.Seed) : P.branchKernel K i =
      ((P.machine i).runKernel (P.init i) (P.init_measurable i) K (P.calls i)).map
        (fun s => (P.read i s, P.calls i)) := by
  apply Kernel.ext
  intro x
  rw [P.branchKernel_apply, Kernel.map_apply (f := fun s => (P.read i s, P.calls i)) _
    ((P.read_measurable i).prodMk measurable_const)]

theorem pair_branch (P : OracleProgram dx dy X Y) (Q : OracleProgram dx dy X Z)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (i : P.Seed) (j : Q.Seed) :
    (P.pair Q).branchKernel K (i, j) = (P.branchKernel K i ×ₖ Q.branchKernel K j).map pairCost := by
  rw [branchKernel_eq_map, P.branchKernel_eq_map, Q.branchKernel_eq_map]
  change (((P.machine i).independentPair (Q.machine j) (P.calls i)).runKernel
    (fun x => (P.init i x, Q.init j x)) ((P.init_measurable i).prodMk (Q.init_measurable j)) K
    (P.calls i + Q.calls j)).map (fun z => ((P.read i z.1, Q.read j z.2), P.calls i + Q.calls j)) = _
  rw [OracleMachine.independentPair_run,
    Kernel.map_prod_map _ _ ((P.read_measurable i).prodMk measurable_const) ((Q.read_measurable j).prodMk measurable_const),
    ← Kernel.map_comp_right _
      (((P.read_measurable i).prodMk measurable_const).prodMap ((Q.read_measurable j).prodMk measurable_const))
      pairCost_measurable]
  rfl

theorem pair_law (P : OracleProgram dx dy X Y) (Q : OracleProgram dx dy X Z)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] :
    (P.pair Q).lawKernel K = (P.lawKernel K ×ₖ Q.lawKernel K).map pairCost := by
  change mixtureKernel (P.seedLaw.prod Q.seedLaw) ((P.pair Q).branchKernel K) =
    (mixtureKernel P.seedLaw (P.branchKernel K) ×ₖ mixtureKernel Q.seedLaw (Q.branchKernel K)).map pairCost
  rw [mixtureKernel_pair, mixtureKernel_map _ _ _ pairCost_measurable]
  congr 1
  funext s
  exact P.pair_branch Q K s.1 s.2

def sum (P : OracleProgram dx dy X (Euclid d)) : ℕ → OracleProgram dx dy X (Euclid d)
  | 0 => pure (fun _ => 0) measurable_const
  | n + 1 => ((P.sum n).pair P).map (fun z => z.1 + z.2) (measurable_fst.add measurable_snd)

theorem sum_law (P : OracleProgram dx dy X (Euclid d))
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    (P.sum n).lawKernel K = costedSumKernel (P.lawKernel K) n := by
  induction n with
  | zero =>
    rw [sum, pure_law, taggedKernel, Kernel.deterministic_map (g := fun r : Euclid d => (r, (0 : ℕ))) _
      (measurable_id.prodMk measurable_const)]
    rfl
  | succ n ih =>
    rw [sum, map_law, pair_law, ih,
      ← Kernel.map_comp_right _ (f := pairCost)
        (g := fun z : (Euclid d × Euclid d) × ℕ => (z.1.1 + z.1.2, z.2))
        pairCost_measurable ((measurable_fst.fst.add measurable_fst.snd).prodMk measurable_snd)]
    rfl

def batch (P : OracleProgram dx dy X (Euclid d)) (b : ℕ) : OracleProgram dx dy X (Euclid d) :=
  (P.sum b).map (fun r => (b : ℝ)⁻¹ • r) (measurable_const.smul measurable_id)

theorem batch_law (P : OracleProgram dx dy X (Euclid d))
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (b : ℕ) :
    (P.batch b).lawKernel K = costedBatchKernel (P.lawKernel K) b := by
  rw [batch, map_law, sum_law]
  rfl

theorem batch_original (P : OracleProgram dx dy X (Euclid d))
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (b : ℕ) :
    (P.batch b).originalKernel K = costedBatchKernel (P.originalKernel K) b := by
  rw [originalKernel_eq_law, batch_law, P.originalKernel_eq_law]

end OracleProgram
end FreshGradientMinimax
