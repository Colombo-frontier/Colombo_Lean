import FreshGradientMinimax.OracleResponse

/-! A parameter-dependent response adapter is implemented inside the
original one-call state machine. Fixing the parameter gives exactly the
machine driven by the transformed oracle, for every finite run length. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace OracleMachine
variable {dx dy : ℕ} {State Seed Θ : Type*}
variable [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Θ]

def adaptResponses (M : OracleMachine dx dy State)
    (T : Θ × (Joint dx dy × Joint dx dy) → Joint dx dy) (hT : Measurable T) :
    OracleMachine dx dy (Θ × State) where
  query n s := M.query n s.2
  update n p := (p.1.1, M.update n (p.1.2, T (p.1.1, (M.query n p.1.2, p.2))))
  output n s := M.output n s.2
  query_measurable n := (M.query_measurable n).comp measurable_snd
  update_measurable n := measurable_fst.fst.prodMk ((M.update_measurable n).comp
    (measurable_fst.snd.prodMk (hT.comp (measurable_fst.fst.prodMk
      (((M.query_measurable n).comp measurable_fst.snd).prodMk measurable_snd)))))
  output_measurable n := (M.output_measurable n).comp measurable_snd

theorem adaptResponses_step_fixed (M : OracleMachine dx dy State)
    (T : Θ × (Joint dx dy × Joint dx dy) → Joint dx dy) (hT : Measurable T)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (θ : Θ) (n : ℕ) :
    ((M.adaptResponses T hT).stepKernel K n).comap (fun s => (θ, s)) measurable_prodMk_left =
      (M.stepKernel (responseTransformKernel K (fun p => T (θ, p))) n).map (fun s => (θ, s)) := by
  letI : IsMarkovKernel (responseTransformKernel K (fun p => T (θ, p))) :=
    responseTransformKernel_markov K _ (hT.comp measurable_prodMk_left)
  apply Kernel.ext
  intro s
  rw [Kernel.comap_apply, stepKernel_apply, Kernel.map_apply _ measurable_prodMk_left, stepKernel_apply]
  change (K (M.query n s)).map (fun r => (θ, M.update n (s, T (θ, (M.query n s, r))))) =
    (((responseTransformKernel K (fun p => T (θ, p))) (M.query n s)).map (fun r => M.update n (s, r))).map (fun w => (θ, w))
  rw [responseTransformKernel_apply K (fun p : Joint dx dy × Joint dx dy => T (θ, p)) (hT.comp measurable_prodMk_left),
    Measure.map_map (g := fun r : Joint dx dy => M.update n (s, r))
      (f := fun r : Joint dx dy => T (θ, (M.query n s, r))) ((M.update_measurable n).comp measurable_prodMk_left)
      ((hT.comp measurable_prodMk_left).comp measurable_prodMk_left)]
  simp only [Function.comp_def]
  rw [Measure.map_map (g := fun w : State => (θ, w))
      (f := fun r : Joint dx dy => M.update n (s, T (θ, (M.query n s, r)))) measurable_prodMk_left
      (((M.update_measurable n).comp measurable_prodMk_left).comp
        ((hT.comp measurable_prodMk_left).comp measurable_prodMk_left))]
  rfl

theorem adaptResponses_run_fixed (M : OracleMachine dx dy State)
    (T : Θ × (Joint dx dy × Joint dx dy) → Joint dx dy) (hT : Measurable T)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (θ : Θ)
    (init : Seed → State) (hi : Measurable init) (n : ℕ) :
    (M.adaptResponses T hT).runKernel (fun x => (θ, init x)) (measurable_const.prodMk hi) K n =
      (M.runKernel init hi (responseTransformKernel K (fun p => T (θ, p))) n).map (fun s => (θ, s)) := by
  induction n with
  | zero =>
    rw [runKernel, runKernel, Kernel.deterministic_map _ measurable_prodMk_left]
    rfl
  | succ n ih =>
    rw [runKernel, runKernel, ih, Kernel.comp_map _ _ measurable_prodMk_left,
      M.adaptResponses_step_fixed T hT K θ n, Kernel.map_comp]

end OracleMachine
end FreshGradientMinimax
