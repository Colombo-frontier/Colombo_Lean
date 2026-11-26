import FreshGradientMinimax.OracleProgram

/-! Closure under adaptive sequential composition is implemented by a
single compiled original-query policy. Both random seeds are sampled
independently at the start; the second initial state uses the first output.
The cost equality is an equality of stopped transcript lengths. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace OracleMachine
variable {dx dy : ℕ} {A B State : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace State]

theorem runKernel_init_comp (M : OracleMachine dx dy State) (init : B → State) (hi : Measurable init)
    (f : A → B) (hf : Measurable f) (K : Kernel (Joint dx dy) (Joint dx dy)) (n : ℕ) :
    M.runKernel (init ∘ f) (hi.comp hf) K n = (M.runKernel init hi K n).comap f hf := by
  rw [← M.runKernel_precompose (init ∘ f) (hi.comp hf) K n, ← M.runKernel_precompose init hi K n]
  rfl

end OracleMachine
namespace OracleProgram
variable {dx dy : ℕ} {X Y Z : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
variable (P : OracleProgram dx dy X Y) (Q : OracleProgram dx dy Y Z)

def chain : OracleProgram dx dy X Z where
  Seed := P.Seed × Q.Seed
  seedLaw := P.seedLaw.prod Q.seedLaw
  State := P.State × Q.State
  machine s := (P.machine s.1).chain (Q.machine s.2) (P.calls s.1)
    (Q.init s.2 ∘ P.read s.1) ((Q.init_measurable s.2).comp (P.read_measurable s.1))
  init s := OracleMachine.chainInitial (Q.init s.2 ∘ P.read s.1) (P.init s.1)
  init_measurable s := OracleMachine.chainInitial_measurable _
    ((Q.init_measurable s.2).comp (P.read_measurable s.1)) _ (P.init_measurable s.1)
  read s z := Q.read s.2 z.2
  read_measurable s := (Q.read_measurable s.2).comp measurable_snd
  calls s := P.calls s.1 + Q.calls s.2

theorem chain_branch (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (i : P.Seed) (j : Q.Seed) :
    (P.chain Q).branchKernel K (i, j) = costedCompose (P.branchKernel K i) (Q.branchKernel K j) := by
  have h := congrArg (fun L : Kernel X Q.State => L.map (Q.read j))
    ((P.machine i).chain_run (Q.machine j) (P.calls i) (Q.calls j)
      (Q.init j ∘ P.read i) ((Q.init_measurable j).comp (P.read_measurable i))
      (P.init i) (P.init_measurable i) K)
  dsimp only at h
  rw [← Kernel.map_comp_right _ (f := Prod.snd) (g := Q.read j) measurable_snd (Q.read_measurable j),
    Kernel.map_comp, OracleMachine.runKernel_init_comp,
    ← Kernel.comap_map_comm _ (P.read_measurable i) (Q.read_measurable j),
    ← Kernel.comp_map _ _ (P.read_measurable i)] at h
  change taggedKernel _ (P.calls i + Q.calls j) = costedCompose
    (taggedKernel (((P.machine i).runKernel (P.init i) (P.init_measurable i) K (P.calls i)).map (P.read i)) (P.calls i))
    (taggedKernel (((Q.machine j).runKernel (Q.init j) (Q.init_measurable j) K (Q.calls j)).map (Q.read j)) (Q.calls j))
  letI := Kernel.IsMarkovKernel.map ((P.machine i).runKernel (P.init i) (P.init_measurable i) K (P.calls i)) (P.read_measurable i)
  letI := Kernel.IsMarkovKernel.map ((Q.machine j).runKernel (Q.init j) (Q.init_measurable j) K (Q.calls j)) (Q.read_measurable j)
  rw [costedCompose_tagged]
  exact congrArg (fun L : Kernel X Z => taggedKernel L (P.calls i + Q.calls j)) h

theorem chain_law (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] :
    (P.chain Q).lawKernel K = costedCompose (P.lawKernel K) (Q.lawKernel K) := by
  change mixtureKernel (P.seedLaw.prod Q.seedLaw) ((P.chain Q).branchKernel K) =
    costedCompose (mixtureKernel P.seedLaw (P.branchKernel K)) (mixtureKernel Q.seedLaw (Q.branchKernel K))
  rw [costedCompose_mixture]
  congr 1
  funext s
  exact P.chain_branch Q K s.1 s.2

theorem chain_original (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] :
    (P.chain Q).originalKernel K = costedCompose (P.originalKernel K) (Q.originalKernel K) := by
  rw [originalKernel_eq_law, P.originalKernel_eq_law, Q.originalKernel_eq_law, P.chain_law]

end OracleProgram
end FreshGradientMinimax
