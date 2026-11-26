import FreshGradientMinimax.OracleMachine
import FreshGradientMinimax.KernelSegments

/-! Output changes, final deterministic updates, and periodic repetition
of original-call state machines preserve exact execution semantics. -/

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace OracleMachine
variable {dx dy : ℕ} {State Seed : Type*} [MeasurableSpace State] [MeasurableSpace Seed]
variable (M : OracleMachine dx dy State)

def withOutput (out : ℕ → State → Euclid dx) (ho : ∀ n, Measurable (out n)) : OracleMachine dx dy State :=
  { M with output := out, output_measurable := ho }

theorem runKernel_congr (N : OracleMachine dx dy State) (init : Seed → State) (hinit : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) (n : ℕ)
    (hstep : ∀ j < n, M.stepKernel K j = N.stepKernel K j) :
    M.runKernel init hinit K n = N.runKernel init hinit K n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [runKernel, runKernel, hstep n (by omega), ih (fun j hj => hstep j (by omega))]

theorem runKernel_withOutput (out : ℕ → State → Euclid dx) (ho : ∀ n, Measurable (out n))
    (init : Seed → State) (hinit : Measurable init) (K : Kernel (Joint dx dy) (Joint dx dy)) (n : ℕ) :
    (M.withOutput out ho).runKernel init hinit K n = M.runKernel init hinit K n :=
  (M.withOutput out ho).runKernel_congr M init hinit K n (fun _ _ => rfl)

theorem runKernel_segment (init : Seed → State) (hinit : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) (n : ℕ) :
    M.runKernel init hinit K n = kernelSegment (M.stepKernel K) 0 n ∘ₖ Kernel.deterministic init hinit := by
  induction n with
  | zero => simp only [runKernel, kernelSegment, Kernel.id_comp]
  | succ n ih => rw [runKernel, ih, kernelSegment, Nat.zero_add, Kernel.comp_assoc]

def endUpdate (b : ℕ) (f : State → State) (hf : Measurable f) : OracleMachine dx dy State where
  query := M.query
  update n s := if n + 1 = b then f (M.update n s) else M.update n s
  output := M.output
  query_measurable := M.query_measurable
  update_measurable n := by
    by_cases h : n + 1 = b
    · simpa only [if_pos h] using hf.comp (M.update_measurable n)
    · simpa only [if_neg h] using M.update_measurable n
  output_measurable := M.output_measurable

theorem endUpdate_step_before (b : ℕ) (f : State → State) (hf : Measurable f)
    (K : Kernel (Joint dx dy) (Joint dx dy)) (n : ℕ) (hn : n + 1 ≠ b) :
    (M.endUpdate b f hf).stepKernel K n = M.stepKernel K n := by
  simp only [stepKernel, endUpdate, if_neg hn]

theorem endUpdate_step_last (n : ℕ) (f : State → State) (hf : Measurable f)
    (K : Kernel (Joint dx dy) (Joint dx dy)) :
    (M.endUpdate (n + 1) f hf).stepKernel K n = (M.stepKernel K n).map f := by
  rw [stepKernel, stepKernel, ← Kernel.map_comp_right _ (M.update_measurable n) hf]
  simp only [endUpdate, if_pos rfl]
  rfl

theorem endUpdate_run (b : ℕ) (hb : 0 < b) (f : State → State) (hf : Measurable f)
    (init : Seed → State) (hinit : Measurable init) (K : Kernel (Joint dx dy) (Joint dx dy)) :
    (M.endUpdate b f hf).runKernel init hinit K b = (M.runKernel init hinit K b).map f := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  rw [runKernel, M.endUpdate_step_last]
  have hprev := (M.endUpdate (n + 1) f hf).runKernel_congr M init hinit K n
    (fun j hj => M.endUpdate_step_before _ _ _ K j (by omega))
  rw [hprev, runKernel, Kernel.map_comp]

def periodic (b : ℕ) : OracleMachine dx dy State where
  query n := M.query (n % b)
  update n := M.update (n % b)
  output n := M.output (n % b)
  query_measurable n := M.query_measurable (n % b)
  update_measurable n := M.update_measurable (n % b)
  output_measurable n := M.output_measurable (n % b)

theorem periodic_step (b : ℕ) (K : Kernel (Joint dx dy) (Joint dx dy)) (n : ℕ) :
    (M.periodic b).stepKernel K n = M.stepKernel K (n % b) := rfl

theorem periodic_first_segment (b : ℕ) (K : Kernel (Joint dx dy) (Joint dx dy)) :
    kernelSegment ((M.periodic b).stepKernel K) 0 b = kernelSegment (M.stepKernel K) 0 b :=
  kernelSegment_congr _ _ _ _ _ (fun j hj => by
    simp only [Nat.zero_add, M.periodic_step, Nat.mod_eq_of_lt hj])

theorem periodic_run_blocks (b n : ℕ) (init : Seed → State) (hinit : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) :
    (M.periodic b).runKernel init hinit K (n * b) =
      iterateKernel (kernelSegment (M.stepKernel K) 0 b) n ∘ₖ Kernel.deterministic init hinit := by
  rw [runKernel_segment, kernelSegment_blocks _ b (fun n j => by
    simp only [periodic_step, Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod, Nat.zero_add,
      Nat.mod_mod]), M.periodic_first_segment]

end OracleMachine
end FreshGradientMinimax
