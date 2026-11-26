import FreshGradientMinimax.IndependentMachines

/-! A genuine sequential program whose second initial state is a
measurable function of the first program's random final state. No extra
oracle call is used for the handoff, including when either duration is zero. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace OracleMachine
variable {dx dy : ℕ} {State Other Seed : Type*}
variable [MeasurableSpace State] [MeasurableSpace Other] [MeasurableSpace Seed]
variable (M : OracleMachine dx dy State) (N : OracleMachine dx dy Other)

def handoff (f : State → Other) (s : State × Other) : State × Other := (s.1, f s.1)

theorem handoff_measurable (f : State → Other) (hf : Measurable f) : Measurable (handoff f) :=
  measurable_fst.prodMk (hf.comp measurable_fst)

def chain (t : ℕ) (f : State → Other) (hf : Measurable f) : OracleMachine dx dy (State × Other) :=
  (M.carry.endUpdate t (handoff f) (handoff_measurable f hf)).sequence N.carryLeft t

def chainInitial (f : State → Other) (init : Seed → State) (q : Seed) : State × Other :=
  (init q, f (init q))

theorem chainInitial_measurable (f : State → Other) (hf : Measurable f)
    (init : Seed → State) (hinit : Measurable init) : Measurable (chainInitial f init) :=
  hinit.prodMk (hf.comp hinit)

theorem handoff_run (t : ℕ) (f : State → Other) (hf : Measurable f)
    (init : Seed → State) (hinit : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] :
    (M.carry.endUpdate t (handoff f) (handoff_measurable f hf)).runKernel
      (chainInitial f init) (chainInitial_measurable f hf init hinit) K t =
      (M.runKernel init hinit K t).map (fun s => (s, f s)) := by
  by_cases ht : t = 0
  · subst t
    rw [runKernel, runKernel, Kernel.deterministic_map (g := fun s : State => (s, f s)) _ (measurable_id.prodMk hf)]
    rfl
  · rw [endUpdate_run _ t (Nat.pos_of_ne_zero ht)]
    apply Kernel.ext
    intro q
    rw [Kernel.map_apply _ (handoff_measurable f hf), runKernel_apply, M.carry_run_apply]
    dsimp only [chainInitial]
    rw [Measure.map_map (f := fun z : State => (z, f (init q))) (g := handoff f)
        (handoff_measurable f hf) (measurable_id.prodMk measurable_const),
      Kernel.map_apply (f := fun s : State => (s, f s)) _ (measurable_id.prodMk hf),
      M.runKernel_apply init hinit K t q]
    rfl

theorem carryLeft_run_snd (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    (N.carryLeft.runKernel (Seed := State × Other) id measurable_id K n).map Prod.snd =
      (N.runKernel id measurable_id K n).comap Prod.snd measurable_snd := by
  apply Kernel.ext
  rintro ⟨s, y⟩
  rw [Kernel.map_apply _ measurable_snd, N.carryLeft_run_apply,
    Measure.map_map (f := fun z : Other => (s, z)) (g := Prod.snd) measurable_snd
      (measurable_const.prodMk measurable_id), Kernel.comap_apply]
  exact Measure.map_id

theorem chain_run (t n : ℕ) (f : State → Other) (hf : Measurable f)
    (init : Seed → State) (hinit : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] :
    ((M.chain N t f hf).runKernel (chainInitial f init) (chainInitial_measurable f hf init hinit) K
      (t + n)).map Prod.snd = N.runKernel f hf K n ∘ₖ M.runKernel init hinit K t := by
  rw [chain, sequence_run, M.handoff_run t f hf init hinit K, Kernel.map_comp, N.carryLeft_run_snd,
    Kernel.comp_map (f := fun s : State => (s, f s)) _ _ (measurable_id.prodMk hf)]
  change (N.runKernel id measurable_id K n).comap f hf ∘ₖ M.runKernel init hinit K t = _
  rw [N.runKernel_precompose]

theorem chain_history (t n : ℕ) (f : State → Other) (hf : Measurable f)
    (init : Seed → State) (hinit : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] :
    (((M.chain N t f hf).compile (chainInitial f init) (chainInitial_measurable f hf init hinit)).historyKernel K
      (t + n)).map (fun h => ((M.chain N t f hf).replay (chainInitial f init) (t + n) h).2) =
      N.runKernel f hf K n ∘ₖ M.runKernel init hinit K t := by
  rw [← M.chain_run N t n f hf init hinit K, runKernel_eq_history,
    ← Kernel.map_comp_right _
      ((M.chain N t f hf).replay_measurable (chainInitial f init) (chainInitial_measurable f hf init hinit) (t + n))
      measurable_snd]
  rfl

end OracleMachine
end FreshGradientMinimax
