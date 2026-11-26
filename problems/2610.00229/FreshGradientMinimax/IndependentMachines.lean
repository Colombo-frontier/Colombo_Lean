import FreshGradientMinimax.MachineSequence

/-! Sequential execution of independent machines, retaining both states.
Freshness of each original response gives the product law; no independent
draw primitive is added to the query model. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace OracleMachine
variable {dx dy : ℕ} {State Other Seed Aux : Type*}
variable [MeasurableSpace State] [MeasurableSpace Other] [MeasurableSpace Seed] [MeasurableSpace Aux]
variable (M : OracleMachine dx dy State)

theorem runKernel_apply (init : Seed → State) (hinit : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) (n : ℕ) (q : Seed) :
    M.runKernel init hinit K n q = M.runKernel id measurable_id K n (init q) := by
  have h := congrArg (fun L : Kernel Seed State => L q) (M.runKernel_precompose init hinit K n)
  exact h.symm

theorem carry_run_apply (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K]
    (n : ℕ) (s : State) (a : Aux) :
    M.carry.runKernel id measurable_id K n (s, a) =
      (M.runKernel id measurable_id K n s).map (fun z => (z, a)) := by
  have h := congrArg (fun L : Kernel State (State × Aux) => L s)
    (M.carry_run_fixed a id measurable_id K n)
  dsimp only at h
  rw [runKernel_apply, Kernel.map_apply (f := fun z : State => (z, a)) _
    (measurable_id.prodMk measurable_const)] at h
  exact h

def carryLeft : OracleMachine dx dy (Aux × State) where
  query n s := M.query n s.2
  update n z := (z.1.1, M.update n (z.1.2, z.2))
  output n s := M.output n s.2
  query_measurable n := (M.query_measurable n).comp measurable_snd
  update_measurable n := measurable_fst.fst.prodMk ((M.update_measurable n).comp
    (measurable_fst.snd.prodMk measurable_snd))
  output_measurable n := (M.output_measurable n).comp measurable_snd

theorem carryLeft_run_fixed (a : Aux) (init : Seed → State) (hinit : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    M.carryLeft.runKernel (fun z => (a, init z)) (measurable_const.prodMk hinit) K n =
      (M.runKernel init hinit K n).map (fun s => (a, s)) :=
  M.runKernel_transport M.carryLeft (fun s => (a, s)) (measurable_const.prodMk measurable_id)
    init hinit K (fun j => M.stepKernel_transport M.carryLeft _ _ K j (fun _ => rfl) (fun _ _ => rfl)) n

theorem carryLeft_run_apply (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K]
    (n : ℕ) (a : Aux) (s : State) :
    M.carryLeft.runKernel id measurable_id K n (a, s) =
      (M.runKernel id measurable_id K n s).map (fun z => (a, z)) := by
  have h := congrArg (fun L : Kernel State (Aux × State) => L s)
    (M.carryLeft_run_fixed a id measurable_id K n)
  dsimp only at h
  rw [runKernel_apply, Kernel.map_apply (f := fun z : State => (a, z)) _
    (measurable_const.prodMk measurable_id)] at h
  exact h

def independentPair (N : OracleMachine dx dy Other) (t : ℕ) : OracleMachine dx dy (State × Other) :=
  M.carry.sequence N.carryLeft t

theorem independentPair_run (N : OracleMachine dx dy Other) (t n : ℕ)
    (init : Seed → State) (hinit : Measurable init) (initN : Seed → Other) (hinitN : Measurable initN)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] :
    (M.independentPair N t).runKernel (fun q => (init q, initN q)) (hinit.prodMk hinitN) K (t + n) =
      M.runKernel init hinit K t ×ₖ N.runKernel initN hinitN K n := by
  rw [independentPair, sequence_run]
  apply Kernel.ext
  intro q
  apply Measure.ext
  intro A hA
  rw [Kernel.comp_apply' _ _ _ hA, runKernel_apply, M.carry_run_apply,
    lintegral_map ((N.carryLeft.runKernel id measurable_id K n).measurable_coe hA)
      (show Measurable (fun z : State => (z, initN q)) from measurable_id.prodMk measurable_const),
    Kernel.prod_apply, Measure.prod_apply hA, M.runKernel_apply init hinit K t q,
    N.runKernel_apply initN hinitN K n q]
  apply lintegral_congr
  intro s
  rw [N.carryLeft_run_apply, Measure.map_apply (f := fun z : Other => (s, z))
    (measurable_const.prodMk measurable_id) hA]

end OracleMachine
end FreshGradientMinimax
