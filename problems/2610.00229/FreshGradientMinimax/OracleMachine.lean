import FreshGradientMinimax.Algorithm
import FreshGradientMinimax.KernelIteration

/-! A measurable state machine executes exactly one original oracle call
per transition. Compilation replays the recorded responses in the existing
unrestricted Algorithm model; its policy is independent of the oracle. -/

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

structure OracleMachine (dx dy : ℕ) (State : Type*) [MeasurableSpace State] where
  query : ℕ → State → Joint dx dy
  update : ℕ → State × Joint dx dy → State
  output : ℕ → State → Euclid dx
  query_measurable : ∀ n, Measurable (query n)
  update_measurable : ∀ n, Measurable (update n)
  output_measurable : ∀ n, Measurable (output n)

namespace Algorithm
variable {dx dy : ℕ} {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm dx dy Seed)

theorem stepKernel_apply (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K]
    (n : ℕ) (s : RunState dx dy Seed n) :
    A.stepKernel K n s = (K (A.query n s)).map (fun r => A.append n (s, r)) := by
  rw [stepKernel, Kernel.map_apply _ (A.append_measurable n), Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, Measure.map_map (A.append_measurable n) measurable_prodMk_left]
  rfl

end Algorithm

namespace OracleMachine
variable {dx dy : ℕ} {State Seed : Type*} [MeasurableSpace State] [MeasurableSpace Seed]

def replay (M : OracleMachine dx dy State) (init : Seed → State) :
    (n : ℕ) → RunState dx dy Seed n → State
  | 0 => fun s => init s.1
  | n + 1 => fun s => M.update n
      (M.replay init n (s.1, fun i => s.2 i.castSucc), (s.2 (Fin.last n)).2)

variable (M : OracleMachine dx dy State)

theorem replay_measurable (init : Seed → State) (hinit : Measurable init) (n : ℕ) :
    Measurable (M.replay init n) := by
  induction n with
  | zero => exact hinit.comp measurable_fst
  | succ n ih =>
    apply (M.update_measurable n).comp
    apply Measurable.prodMk
    · apply ih.comp
      apply measurable_fst.prodMk
      exact measurable_pi_lambda _ (fun i => (measurable_pi_apply i.castSucc).comp measurable_snd)
    · exact measurable_snd.comp ((measurable_pi_apply (Fin.last n)).comp measurable_snd)

def compile (init : Seed → State) (hinit : Measurable init) : Algorithm dx dy Seed where
  query n := M.query n ∘ M.replay init n
  output n := M.output n ∘ M.replay init n
  query_measurable n := (M.query_measurable n).comp (M.replay_measurable init hinit n)
  output_measurable n := (M.output_measurable n).comp (M.replay_measurable init hinit n)

omit [MeasurableSpace Seed] in
theorem replay_initial (init : Seed → State) (seed : Seed) :
    M.replay init 0 (Algorithm.initial seed) = init seed := rfl

theorem replay_append (init : Seed → State) (A : Algorithm dx dy Seed) (n : ℕ)
    (s : RunState dx dy Seed n) (r : Joint dx dy) :
    M.replay init (n + 1) (A.append n (s, r)) = M.update n (M.replay init n s, r) := by
  simp only [replay, Algorithm.append, Fin.snoc_castSucc, Fin.snoc_last]

def stepKernel (K : Kernel (Joint dx dy) (Joint dx dy)) (n : ℕ) : Kernel State State :=
  (Kernel.id ×ₖ K.comap (M.query n) (M.query_measurable n)).map (M.update n)

instance stepKernel_markov (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (M.stepKernel K n) := Kernel.IsMarkovKernel.map _ (M.update_measurable n)

theorem stepKernel_apply (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K]
    (n : ℕ) (s : State) : M.stepKernel K n s = (K (M.query n s)).map (fun r => M.update n (s, r)) := by
  rw [stepKernel, Kernel.map_apply _ (M.update_measurable n), Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, Measure.map_map (M.update_measurable n) measurable_prodMk_left]
  rfl

def runKernel (M : OracleMachine dx dy State) (init : Seed → State) (hinit : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) : ℕ → Kernel Seed State
  | 0 => Kernel.deterministic init hinit
  | n + 1 => M.stepKernel K n ∘ₖ M.runKernel init hinit K n

instance runKernel_markov (init : Seed → State) (hinit : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (M.runKernel init hinit K n) := by
  induction n with
  | zero => dsimp [runKernel]; infer_instance
  | succ n ih =>
    letI := ih
    change IsMarkovKernel (M.stepKernel K n ∘ₖ M.runKernel init hinit K n)
    infer_instance

theorem replay_step_transport (init : Seed → State) (hinit : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    (M.stepKernel K n).comap (M.replay init n) (M.replay_measurable init hinit n) =
      ((M.compile init hinit).stepKernel K n).map (M.replay init (n + 1)) := by
  apply Kernel.ext
  intro s
  rw [Kernel.comap_apply, M.stepKernel_apply,
    Kernel.map_apply _ (M.replay_measurable init hinit (n + 1)), Algorithm.stepKernel_apply,
    Measure.map_map (f := fun r => (M.compile init hinit).append n (s, r))
      (g := M.replay init (n + 1)) (M.replay_measurable init hinit (n + 1))
      (((M.compile init hinit).append_measurable n).comp measurable_prodMk_left)]
  simp only [Function.comp_def, M.replay_append]
  rfl

theorem runKernel_eq_history (init : Seed → State) (hinit : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    M.runKernel init hinit K n = ((M.compile init hinit).historyKernel K n).map (M.replay init n) := by
  induction n with
  | zero =>
    rw [Algorithm.historyKernel, Kernel.deterministic_map _ (M.replay_measurable init hinit 0)]
    rfl
  | succ n ih =>
    rw [runKernel, Algorithm.historyKernel, Kernel.map_comp, ← M.replay_step_transport init hinit K n,
      ← Kernel.comp_map _ _ (M.replay_measurable init hinit n), ← ih]

theorem compiled_outputKernel (init : Seed → State) (hinit : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    (M.compile init hinit).outputKernel K n = (M.runKernel init hinit K n).map (M.output n) := by
  rw [M.runKernel_eq_history init hinit K n,
    ← Kernel.map_comp_right _ (M.replay_measurable init hinit n) (M.output_measurable n)]
  rfl

theorem compiled_outputLaw (init : Seed → State) (hinit : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (ν : Measure Seed) (n : ℕ) :
    (M.compile init hinit).outputLaw ν K n = (M.runKernel init hinit K n ∘ₘ ν).map (M.output n) := by
  rw [Algorithm.outputLaw, M.compiled_outputKernel init hinit K n,
    Measure.map_comp _ _ (M.output_measurable n)]

theorem compiled_internalLaw (init : Seed → State) (hinit : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (ν : Measure Seed) (n : ℕ) :
    (((M.compile init hinit).historyKernel K n) ∘ₘ ν).map (M.replay init n) =
      M.runKernel init hinit K n ∘ₘ ν := by
  rw [Measure.map_comp _ _ (M.replay_measurable init hinit n), ← M.runKernel_eq_history init hinit K n]

theorem runKernel_homogeneous (init : Seed → State) (hinit : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) (L : Kernel State State)
    (hstep : ∀ n, M.stepKernel K n = L) (n : ℕ) :
    M.runKernel init hinit K n = iterateKernel L n ∘ₖ Kernel.deterministic init hinit := by
  induction n with
  | zero => simp only [runKernel, iterateKernel, Kernel.id_comp]
  | succ n ih => rw [runKernel, hstep, ih, iterateKernel, Kernel.comp_assoc]

end OracleMachine
end FreshGradientMinimax
