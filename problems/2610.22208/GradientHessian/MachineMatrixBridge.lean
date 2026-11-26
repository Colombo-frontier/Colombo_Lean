import GradientHessian.MachineCompiler

/-!
# The mixed-machine model compiles to a fixed-budget matrix policy

Both charged modes in this bridge call the selected matrix-vector oracle.
Their continuation maps remain different. Internal computation and arbitrary
measurable final-state decoding are preserved. Applying this bridge to the
manuscript's nonlinear oracle still requires its concrete matrix simulation.
-/

namespace GradientHessian.MachineMatrixBridge

open MeasureTheory Matrix LowRank MachineCompiler
noncomputable section
universe u v w

variable {d : ℕ} {Seed : Type u} {State : Type v} {O : Type w}
  [MeasurableSpace Seed] [MeasurableSpace State] [MeasurableSpace O]

def lower (P : Machine.Policy Seed State (Fin d → ℝ) (Fin d → ℝ) (Fin d → ℝ))
    (decode : State → O) (hd : Measurable decode) (fallback : O) : Program d State O where
  mode := fun s => if P.mode s = 0 then 0 else if P.mode s = 1 then 1 else 2
  think := P.think
  query := P.point
  next := fun p => if P.mode p.1 = 2 then P.ordinaryNext p else P.richNext p
  output := decode
  fallback := fallback
  mode_measurable := Measurable.ite (P.mode_measurable (measurableSet_singleton 0))
    measurable_const (Measurable.ite (P.mode_measurable (measurableSet_singleton 1))
      measurable_const measurable_const)
  think_measurable := P.think_measurable
  query_measurable := P.point_measurable
  next_measurable := Measurable.ite
    ((P.mode_measurable.comp measurable_fst) (measurableSet_singleton 2))
    P.ordinaryNext_measurable P.richNext_measurable
  output_measurable := hd

theorem lower_halt_iff
    (P : Machine.Policy Seed State (Fin d → ℝ) (Fin d → ℝ) (Fin d → ℝ))
    (decode : State → O) (hd : Measurable decode) (fallback : O) (s : State) :
    (lower P decode hd fallback).mode s = 0 ↔ P.mode s = 0 := by
  simp only [lower]
  split_ifs <;> simp_all

theorem lower_step
    (P : Machine.Policy Seed State (Fin d → ℝ) (Fin d → ℝ) (Fin d → ℝ))
    (decode : State → O) (hd : Measurable decode) (fallback : O)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) :
    (lower P decode hd fallback).step oracle = P.step oracle oracle := by
  funext s
  simp only [Program.step, lower, Machine.Policy.step]
  split_ifs <;> simp_all

theorem mixed_run_eq_iterate
    (P : Machine.Policy Seed State (Fin d → ℝ) (Fin d → ℝ) (Fin d → ℝ))
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (n : ℕ) (seed : Seed) :
    P.run oracle oracle n seed = (P.step oracle oracle)^[n] (P.initial seed) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change P.step oracle oracle (P.run oracle oracle n seed) = _
    rw [ih, Function.iterate_succ_apply']

theorem lower_calls_eq_total
    (P : Machine.Policy Seed State (Fin d → ℝ) (Fin d → ℝ) (Fin d → ℝ))
    (decode : State → O) (hd : Measurable decode) (fallback : O)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (n : ℕ) (seed : Seed) :
    (lower P decode hd fallback).calls oracle n (P.initial seed) =
      P.ordinaryCount oracle oracle n seed + P.richCount oracle oracle n seed := by
  rw [Program.calls_eq_sum, lower_step]
  unfold Machine.Policy.ordinaryCount Machine.Policy.richCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mixed_run_eq_iterate]
  simp only [lower]
  have hm : ∀ m : Fin 4,
      (if (if m = 0 then (0 : Fin 3) else if m = 1 then 1 else 2) = 2
        then (1 : ℕ) else 0) = (if m = 2 then 1 else 0) + (if m = 3 then 1 else 0) := by
    decide
  exact hm _

def initialConfig
    (P : Machine.Policy Seed State (Fin d → ℝ) (Fin d → ℝ) (Fin d → ℝ)) (N : ℕ) :
    MeasurableStateMap Seed (ℕ × State) :=
  ⟨fun seed => (N, P.initial seed), measurable_const.prodMk P.initial_measurable⟩

/-- A legal mixed run has exactly the same decoded output after compilation.
No restriction is imposed on query vectors, output locations or internal time. -/
theorem padded_mixed_run_at_halt
    (P : Machine.Policy Seed State (Fin d → ℝ) (Fin d → ℝ) (Fin d → ℝ))
    (decode : State → O) (hd : Measurable decode) (fallback : O)
    (W : Matrix (Fin d) (Fin d) ℝ) (hW : Wᵀ = W)
    (G H N : ℕ) (seed : Seed)
    (hc : P.HasCaps (fun v => W *ᵥ v) (fun v => W *ᵥ v) G H)
    (hh : P.mode (P.run (fun v => W *ᵥ v) (fun v => W *ᵥ v) N seed) = 0) :
    let compiled := (lower P decode hd fallback).compile (G + H) (initialConfig P N)
    readPaddedSymmetricOutput d (G + H) compiled
      (runAmbientOracle d (G + H) (padSymmetricPolicy d (G + H) compiled) W seed) =
      (true, decode (P.run (fun v => W *ᵥ v) (fun v => W *ᵥ v) N seed)) := by
  dsimp only
  rw [Program.padded_simulates _ _ _ W hW seed]
  · change (lower P decode hd fallback).eval _ N (P.initial seed) = _
    have he := (lower P decode hd fallback).eval_eq_at_halt (fun v => W *ᵥ v) N
      (P.initial seed)
    rw [lower_step, ← mixed_run_eq_iterate] at he
    apply he
    exact (lower_halt_iff P decode hd fallback _).mpr hh
  · change (lower P decode hd fallback).calls _ N (P.initial seed) ≤ G + H
    rw [lower_calls_eq_total]
    exact Nat.add_le_add (hc seed N).1 (hc seed N).2

end
end GradientHessian.MachineMatrixBridge
