import FreshGradientMinimax.MachineComposition

/-! Sequential programs and preservation of extra memory for original-call
machines. The second program starts at local time zero after the first
program's prescribed number of calls. -/

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace OracleMachine
variable {dx dy : ℕ} {State Other Seed Aux : Type*}
variable [MeasurableSpace State] [MeasurableSpace Other] [MeasurableSpace Seed] [MeasurableSpace Aux]
variable (M : OracleMachine dx dy State)

def sequence (N : OracleMachine dx dy State) (t : ℕ) : OracleMachine dx dy State where
  query n := if n < t then M.query n else N.query (n - t)
  update n := if n < t then M.update n else N.update (n - t)
  output n := if n < t then M.output n else N.output (n - t)
  query_measurable n := by split <;> apply query_measurable
  update_measurable n := by split <;> apply update_measurable
  output_measurable n := by split <;> apply output_measurable

theorem sequence_step_before (N : OracleMachine dx dy State) (t : ℕ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) {j : ℕ} (hj : j < t) :
    (M.sequence N t).stepKernel K j = M.stepKernel K j := by
  simp only [stepKernel, sequence, if_pos hj]

theorem sequence_step_after (N : OracleMachine dx dy State) (t j : ℕ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) :
    (M.sequence N t).stepKernel K (t + j) = N.stepKernel K j := by
  simp only [stepKernel, sequence, show ¬t + j < t by omega, if_false, Nat.add_sub_cancel_left]

theorem sequence_run (N : OracleMachine dx dy State) (t n : ℕ)
    (init : Seed → State) (hinit : Measurable init) (K : Kernel (Joint dx dy) (Joint dx dy)) :
    (M.sequence N t).runKernel init hinit K (t + n) =
      N.runKernel id measurable_id K n ∘ₖ M.runKernel init hinit K t := by
  rw [runKernel_segment, kernelSegment_split, Nat.zero_add]
  have hfirst : kernelSegment ((M.sequence N t).stepKernel K) 0 t =
      kernelSegment (M.stepKernel K) 0 t :=
    kernelSegment_congr _ _ _ _ _ (fun j hj => by
      simpa only [Nat.zero_add] using M.sequence_step_before N t K hj)
  have hsecond : kernelSegment ((M.sequence N t).stepKernel K) t n =
      kernelSegment (N.stepKernel K) 0 n :=
    kernelSegment_congr _ _ _ _ _ (fun j _ => by
      simpa only [Nat.zero_add] using M.sequence_step_after N t j K)
  rw [hfirst, hsecond, runKernel_segment, runKernel_segment]
  change (_ ∘ₖ _) ∘ₖ _ = (_ ∘ₖ Kernel.id) ∘ₖ (_ ∘ₖ _)
  rw [Kernel.comp_id, Kernel.comp_assoc]

theorem stepKernel_transport (N : OracleMachine dx dy Other) (f : State → Other) (hf : Measurable f)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ)
    (hq : ∀ s, N.query n (f s) = M.query n s)
    (hu : ∀ s r, N.update n (f s, r) = f (M.update n (s, r))) :
    (N.stepKernel K n).comap f hf = (M.stepKernel K n).map f := by
  apply Kernel.ext
  intro s
  rw [Kernel.comap_apply, N.stepKernel_apply, hq, Kernel.map_apply _ hf,
    M.stepKernel_apply, Measure.map_map (f := fun r => M.update n (s, r)) (g := f)
      hf ((M.update_measurable n).comp measurable_prodMk_left)]
  simp only [Function.comp_def, hu]

theorem runKernel_transport (N : OracleMachine dx dy Other) (f : State → Other) (hf : Measurable f)
    (init : Seed → State) (hinit : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy))
    (hs : ∀ j, (N.stepKernel K j).comap f hf = (M.stepKernel K j).map f) (n : ℕ) :
    N.runKernel (f ∘ init) (hf.comp hinit) K n = (M.runKernel init hinit K n).map f := by
  induction n with
  | zero => rw [runKernel, runKernel, Kernel.deterministic_map _ hf]
  | succ n ih =>
    rw [runKernel, ih, Kernel.comp_map _ _ hf, hs, ← Kernel.map_comp, runKernel]

theorem runKernel_precompose (f : Seed → State) (hf : Measurable f)
    (K : Kernel (Joint dx dy) (Joint dx dy)) (n : ℕ) :
    (M.runKernel id measurable_id K n).comap f hf = M.runKernel f hf K n := by
  rw [runKernel_segment, runKernel_segment, ← Kernel.comp_deterministic_eq_comap]
  change (_ ∘ₖ Kernel.id) ∘ₖ _ = _
  rw [Kernel.comp_id]

def carry : OracleMachine dx dy (State × Aux) where
  query n s := M.query n s.1
  update n z := (M.update n (z.1.1, z.2), z.1.2)
  output n s := M.output n s.1
  query_measurable n := (M.query_measurable n).comp measurable_fst
  update_measurable n := ((M.update_measurable n).comp
    (measurable_fst.fst.prodMk measurable_snd)).prodMk measurable_fst.snd
  output_measurable n := (M.output_measurable n).comp measurable_fst

theorem carry_run_fixed (a : Aux) (init : Seed → State) (hinit : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    M.carry.runKernel (fun z => (init z, a)) (hinit.prodMk measurable_const) K n =
      (M.runKernel init hinit K n).map (fun s => (s, a)) :=
  M.runKernel_transport M.carry (fun s => (s, a)) (measurable_id.prodMk measurable_const)
    init hinit K (fun j => M.stepKernel_transport M.carry _ _ K j (fun _ => rfl) (fun _ _ => rfl)) n

end OracleMachine
end FreshGradientMinimax
