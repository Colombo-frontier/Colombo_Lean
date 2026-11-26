import FreshGradientMinimax.CountableMixture
import FreshGradientMinimax.MachineChain

/-! Measurable selection by any countable initial seed, including finite
tuples of independently chosen labels. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace OracleMachine
variable {dx dy : ℕ} {I State Seed Out : Type*}
variable [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
variable [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Out]

def labelSelect (M : I → OracleMachine dx dy State) : OracleMachine dx dy (State × I) where
  query n s := (M s.2).query n s.1
  update n z := ((M z.1.2).update n (z.1.1, z.2), z.1.2)
  output n s := (M s.2).output n s.1
  query_measurable n := measurable_from_prod_countable (fun i => (M i).query_measurable n)
  update_measurable n := by
    have hh : Measurable (fun z : (State × Joint dx dy) × I => (M z.2).update n z.1) :=
      measurable_from_prod_countable (fun i => (M i).update_measurable n)
    exact (hh.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)).prodMk measurable_fst.snd
  output_measurable n := measurable_from_prod_countable (fun i => (M i).output_measurable n)

def labelInitial (init : I → Seed → State) (s : Seed × I) : State × I := (init s.2 s.1, s.2)

theorem labelInitial_measurable (init : I → Seed → State) (hinit : ∀ i, Measurable (init i)) :
    Measurable (labelInitial init) := (measurable_from_prod_countable hinit).prodMk measurable_snd

def labelRead (read : I → State → Out) (s : State × I) : Out := read s.2 s.1

theorem labelRead_measurable (read : I → State → Out) (hread : ∀ i, Measurable (read i)) :
    Measurable (labelRead read) := measurable_from_prod_countable hread

theorem labelSelect_run_fixed (M : I → OracleMachine dx dy State) (i : I)
    (init : Seed → State) (hinit : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    (labelSelect M).runKernel (fun q => (init q, i)) (hinit.prodMk measurable_const) K n =
      ((M i).runKernel init hinit K n).map (fun s => (s, i)) :=
  (M i).runKernel_transport (labelSelect M) (fun s => (s, i)) (measurable_id.prodMk measurable_const)
    init hinit K (fun j => (M i).stepKernel_transport (labelSelect M) _ _ K j
      (fun _ => rfl) (fun _ _ => rfl)) n

theorem labelSelect_run_apply (M : I → OracleMachine dx dy State) (init : I → Seed → State)
    (hinit : ∀ i, Measurable (init i)) (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K]
    (n : ℕ) (q : Seed) (i : I) :
    (labelSelect M).runKernel (labelInitial init) (labelInitial_measurable init hinit) K n (q, i) =
      ((M i).runKernel (init i) (hinit i) K n q).map (fun s => (s, i)) := by
  have h := congrArg (fun L : Kernel Seed (State × I) => L q)
    (labelSelect_run_fixed M i (init i) (hinit i) K n)
  dsimp only at h
  rw [runKernel_apply, Kernel.map_apply (f := fun s : State => (s, i)) _
    (measurable_id.prodMk measurable_const)] at h
  rw [runKernel_apply]
  exact h

theorem labelSelect_stopped_apply (M : I → OracleMachine dx dy State) (init : I → Seed → State)
    (hinit : ∀ i, Measurable (init i)) (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K]
    (T : I → ℕ) (read : I → State → Out) (hread : ∀ i, Measurable (read i)) (q : Seed) (i : I) :
    (labelSelect M).seedStoppedKernel (labelInitial init) (labelInitial_measurable init hinit) K
      (fun s => T s.2) ((measurable_of_countable T).comp measurable_snd) (labelRead read) (q, i) =
      ((M i).runKernel (init i) (hinit i) K (T i) q).map (fun s => (read i s, T i)) := by
  rw [seedStoppedKernel_apply _ _ _ _ _ _ _ (labelRead_measurable read hread), labelSelect_run_apply,
    Measure.map_map (f := fun s : State => (s, i)) (g := fun s : State × I => (labelRead read s, T i))
      ((labelRead_measurable read hread).prodMk measurable_const) (measurable_id.prodMk measurable_const)]
  rfl

end OracleMachine
end FreshGradientMinimax
